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


namespace Q3PackedColumnCache

def pointWords : List Nat := [727165423746277286308656163155855241632176107997488461621221857459814221232746196810842823016801324815971527864104683515406580546784789375740653176718369866052604199228128659692406550152032136773131234409061092131181257695072883040080860369267924200678600168357199944800006719733351023891200603531870587301567001086796983769274003541576373343231617356862367497229285945835179130852896058703745010462899963604451883427209933744070613504292336385342217662377224031494938254961874830087678505012776599484243829148288184912050018418588696804334528507800630466112331505253122567824699997933974080343770033410374180994328343561403832644419698021857547670487218953481109980216264092423501084273010778670285082290664205947794297454124937596873776936590492956555251618778271663580662341245837573313593411347882411166305747313238004175741388471143605438044383424854018014873951709940184506107013918869754940699576379169947311548654972789842284922526848298958679017985176627381810407720289793884972893327974276161827607066078284040370989175837543018407575105752255579080771995758680585691783696891193277129489622637110876713391475690313503780208002753816997223005571626435885957384720652367052608645271568520036623747707393863896781969410648618319918351825706672136079039286669851832485174569209006995893721241065768141070640205570937294547459809358579150812987665818402435744199237449881608688990292523549349834279611455341520718806486202358248536382914730152469081850909296860579870838948236765671714026412924966419911205459179775210518768719595452728762432227174492387879708668662948527169970040859212205620053099128821452772510612023710144104743601994746850770405248738624984977894352241991805799633434687487908396135390462559296438040897491136156017880735305969967464724717697457748530863024301080504339567345937349182547693021850805784652393154644220205928869776779624123385567094378891296353367624994207532556244843492396936602848970619149299683484789744936245236503073649584679845350384403920692051513805145294814651393590292390562730328077399901692602649770469295982057393953731308907178353309958943065457137309169707664903885209082555525937539336192011547616539109308447555685339488505567248706409412482520948067640132410498257903397930726126120294226372349881911694075475092529117045100226908646687953348931885643545698158829488018676793126440279215317333876958407101502846775730433916955900764748809484844403602387854312727204384312633725107998124337110317143861930, 872598508495532743570387395787026289958611329596986153945466228951777065479295436173011387620161589779165833436925620218487896656141747250888783812062043839263125039073754391630887860182438564127757481290873310557417509234087459648097032443121509040814320202028639933760008063680021228669440724238244704761880401304156380523128804249891648011877940828234840996675143135002214957023475270444494012555479956325342260112651920492884736205150803662410661194852668837793925905954249796105214206015331919381092594977945821894460022102306436165201434209360756559334797806303747081389639997520768896412524040092449017193194012273684599173303637626229057204584662744177331976259516910908201301127612934404342098748797047137353156944949925116248532323908591547866301942533925996296794809495005087976312093617458893399566896775885605010889666165372326525653260109824821617848742051928221407328416702643705928839491655003936773858385967347810741907032217958750414821582211952858172489264347752661967471993569131394193128479293940848445187011005051622089090126902706694896926394910416702830140436269431932555387547164533052056069770828376204536249603304580396667606685951723063148861664782840463130374325882224043948497248872636676138363292778341983902022190848006563294847144003822198982209483050808395072465489278921769284768246685124753456951771230294980975585198982082922893039084939857930426788351028259219801135533746409824862567783442829898243659497676182962898221091156232695845006737884118806056831695509959703893446551015730252622522463514543274514918672609390865455650402395538232603964049031054646744063718954585743327012734428452172925692322393696220924486298486349981973473222690390166959560121624985490075362468555071155725649076989363387221456882367163960957669661236949298237035629161296605207480815124819019057231626220966941582871785573064247114643732135548948062680513254669555624041149993049039067493812190876323923418764742979159620181747693923494283803688379501615814420461284704830461816566174353777581672308350868675276393692879882031123179724563155178468872744477570688614023971950731678548564771003649197884662250899066631125047203430413857139846931170137066822407386206680698447691294979025137681168158892597909484077516871351344353071646819858294032890570111034940454120272290376025544018718262772254837790595385622412151751728335058380800652350088521803416130876520700347080917698571381813284322865425175272645261175160470129597749204532380572634316, 1026586480582979698318102818572972105833660387761160181112313210531502429975641689615307514847248929151959804043441906139397525477813820295163275073014169222662500045969122813683397482567574781326773507401027424185197069687161717233055332286025304753899200237680752863247068310211789680787577322633229064425741648593125153556622122646931350602209342150864518819617815452943782302380559141699404720653505830970990894250178729991629101417824474896953719052767845691522265771710882113064957889429802258095403052915230378699364731885066395488472275540424419481570350360357349507517223526495022231073557694226410608462581190910217175498004279560269479064217250287267449383834725777539060354267779922828637763233878878985121361111705794254410038028127754762195649344157559995643288011170594221148602463079363403999490466795159535306929019018085090030180306011558613668057343590503789890974607885463183445693519594122278557480454079232718519890626138775000488025390837591597849987369820885484667614110081331051991915857992871586406102365888296025987164855179654935172854582247549062153106395611096391241632408428862414183611495092207299454411298005388701961890218766733015469249017391577015447499206920263581115879116320749030751015638562755275178849636291772427405702522357437881155540568295068700085253516798731493276197937276617357008178554388582330559511998802450497521222452870421094619751001209716729177806510289893911603020921697446939110187644324921132821436577830861995111772632804845654184507877070540828109937118842035591320614662958286205311669026599283371124294591053574391298781234154181937345957316417159698031779687562884909324343908698466142264101527630999978792321438459282549364188378382335870676897021829495477324293031752192220260537508667251718773729013219940350867100740189760712008800958970375316537919560259961107744555041850663820134874978982998762426682956770199477204754294109469457726463308459854498733433840874093128964919703169321757980945515740590136252259366217299800543313607263945620684320362765727853266345521035155330733152617133123739375144405267730221898851731706743151233605612945469644570190883410666624852996709918133949576290507258984784496949866125506704056107405857676632566080186932468128804797078672178052180084290376303875332812435424746988769553261518089441816492609720908535103283053394849896649119680394186330353708647162966827548389266494941584801079645378096250922732782853147379582660206071141328938528475920447732510960, 1086503979449690575651844228217308999170255352027375755885405421262913077639589648153165930110707037857327107781385986264265085330604510195659186069493595441884046741259149437050132744196032453388647447521709958670714408384855980884790079306610439272609270290463676182113628717422594525969731641074857219936971705904007944620238199844223063672377202587685405132046870829574742358939735745300537291897873875580192697416531574154564652084234463704168916662851572093751191789515019201376142202042436631135990779739076509751856836858902955536437583451344132680883794933919062513792547856835198625883298415679313951368957525010035298581545385371180149048510085907146872499622744791792312904127767077857546582099669475034836615651299517654472880714594355234697340940120063497334530502094947969464668754698781501509188353962192193009668066820697060265404837490832462714831118508237474125856394337922124113730106340860932947994877469071204036615759960104280672151386411770095778974959499147283383622715728101346855257250482727904678832075959597350461123893419712616214071775763942976286556185238203184504762704640663722404444850836888659344746587772240182621144511690861401586131255760735207010582818219111650052603578362816094802631337311554221200961482767945915386580101483358380055669395238360647561046523615778078486870968635174790296593645111651338179716979277301693874601195255854232438024405949583464343826345520821571813313971601967188474595483487854272869380346964958998717518117209797735168039465226408969828415939007913155016370382586201742586669164338541155431160034111176009467970800349951311121013190916215711535580058432313989635103280801489457960449865819579744091484168330446900494393925758736796980996069796197547985243986912826007435277051974678861892818255236668386909927631640524955900365217276039245518731985956067787184898721336111124812007759857492853618901806387137189882074583648932655648241322572297368309315193454293117036802176116947541520689417437511739535465165801967104076970043485576688039436337246217805791618605920475680775943625915212673579919370555730040297617396981455786519613722650458145226038600341250280000058774699347993325879447371376892541518924459680247094401612425245307618575139477164712198073172758102841217832400709551183231614717647981248814468821528872872272708131689054947657949379468479268048873747343263353526104093495435708533703815123051015820597912618062958175032361618895281114722085802920005724823912258217055420160, 1090731492377649913076371140926090508772288022347454197342151662049370236722216185228086315727659756087542381786669313644178532646766436284737006116912929052480815466086667985449476379848717017461066159075763944044793663983039270860309579287128095894281232142914478590317223256735391291218709799496421963380887780564207862618897899570488789617056638427895664654281211004766489910727727759201869928567754368100035673717570919126251088544271996521425780323822125382487425579684333175106262840178463933895343170737038950968066359623128053628535048757661064396306004795648304940834022134014394738759997701517820826227420441665932867910905808846005834356158743488457009559411929525941069176013153662608964473953666693646214666782585377199491581365863433169067968554135514558442306342887694230846994624550135534847376599232197823557564146242081587332064559992017476950946319619359444248109371748486692855799489698611814707943283617576829210629477688865539069261394552743917809639143313973756326583543848257378462564429616241730696091062171503561065325895232765192882741203763695870971284992282098111218660418751522767664574753593551408755505554155839084715661988085587581566973581015461353733620165345862546046674315694133031863752093388494672036462729057916866275750767303860636596466131368879010701380485553645594699302909325196756079672385052501103827150151831976334641466070132492510498840375913377104324412513915893203117957074929225098251683568818116610778983960015236926371712955543693067918514007296273844438273669212942647585898655890739354078797284894964671836167065386613546773833634383996775276160029552156249040219772103984039642838626279683147201335391793975777396995993145807139132507822505131625600404251400452096938297028960261358945050090842090295278274847010557189245433247492155849346122470894688100480162577170477926277810346432479715635924966607323646570559953092490196327592825540237991980241590165503279915261077067074366481305045563364399525904422723786141683588265993912136830065659108641858179205570900455649154556530215297251775499077409916111817294890330692445660632067110242139656963639480277435505310459643431014873489279414979373131151267245336657370517617194123667803452567018352064922735181294255470115135422465189162296162920296668926670039756221615001022346654653517921366037709997197050769974298091004898049521668450005074312059455258124511891747278706315095791213785601531930729995714415221299954221210448230969019753953267507156418560, 1090748135365456339041586926824709096400964067164273332347272707540109023476350483456643682700482416018057609895981362120404606980048375087448667425214590816869671144547395038055582970986878455636444962424714107236239490619974692554770930709212877821728916669614260327992795699918566977659395175021578144334544566109855586642133164142480791907459073081590624358274300179425040837504737754591061664838562273108983506886107634298866042884653729319819199997516446804694739144110610717674156946529148702714412442293984696868969709907445224692898230111221050144866923794893547112852427041007695329043678419482870554145720540889865230465166845682064128327460786411382323751884924288490359559578197608978570342104424944587739380487102228316436132266546300897104300298367464939913764498334082754312722554117819014494666733843304428703937824198941703283915032685136815704633686814941668193778404358975865825028806933982931557049500470592340750507523610764520132237088741246609468819349337613959440828784317324935031505062497594936585663442849809668662650964255879591527000676094851237579633838846544771148541303921518249715058663926914944350215064247014897203907073996515109866185678977480329325325801747949437443546148220516763024497923624659148936397529559134468581007943125037851605844897637030937792984208879998260560834990466014491803030020045397864796326702999835042686266982263606726267146269373602788359121917286258255297088099245591502185867918926029084430605200919372173516522535733737890028181875115540306551779084866614357067231533631720626002919587235295062368071686593937750462360071885117835669805146321374038164582655652795571977548739307436252124465110216812285016292939828102403759493188093620266844902118992158588255074301105296020131705096904108125908453231286645621791511653515435611337191921902927077389109450451989403004404527133421488734171726166453908082112971477795474787089400560567367842496129965928562701168456383421601224547224975507428722506692020725843928961435818309035149891715365798426895257374225068707636935783558936310339766210019945402769632483047091147946123851035813219440350036499475353738431721176746185131364175201392263406813394131677632259165477572009757420066823456072165146952257899881163435108097311824032068432359543340248227743649736365547338111070004318372011931585654645314294836757658558013694582114506887325604913720922722968365137005114262182509113579006044876988892546771973980841489093151046977170736321405274931855360, 1090748135619415929403854669820128643835281822143174671095392721590677921920417072578689030872885679376536174029528239896742254073353278082923030058229357091300030393146888777261730166167240147960083923101996823490514355455651568890737193309875090994887952495597058554419219395583801974058669822774425700320602000555580027419219660782965643544761919466940595449891933698401109894205870007440326040697196084961016514337994471542752611988248099510093894277317118938299181052534179992180611763502713740568706813166286568129787497207891105101070642977075903571570054027644364590446601280785149886722456526311428692503745869033851011170379573239871025633307907777362710306567563441148121858767949811499260469124776695938902641931594003381934561985005343743685083799012958615340497526215585095341939983925335426324943931358772634914039415810241181336029872642177025788124259913276625707191883433362498148979089190612769477364849156296598604956531440099537350932558545961732221916191503815951153776287037593938459242959091504280127175810734425619861520616741230751469122342495262459811324635237600645624320878844480106463393239977750409859338365102275402708239345773880027238141707183621557733481314949378274404868584905321709416744565607290993339377141986944120719563564133545054356921532678282631495561640293652704448981407979637281048067370092943735415862513219631905132205243835345916182893926006276981822640099165954635101713781042208879607159383576070856276803186793994557281304652875534793746532044826511343908913238927973380729497620328575369613527557267407888667221403469768087071709689761333129469855333306317190610121128804688744301302209854694241778786633133327396692416385648538584937903813623713078893779055091594531543783419179722909182516033055000345688034320365228169710990474860995658072338681123651241223172931351929918827568679587283744611196323840052692029991663662335786495300388236002058368899453352397682826240056654577137531924806502740465564271415492629087478374350216697724571799736835532009208639156739698175298800515035510452484116660223014932861307476880632787267150057929595142785268236485943223275300709970934124908318484485834183562070916059435823162768771276983699787719886834170973112315811783258262042268793707899620037982010519892205757909218844019984162560417654567467164875084760799557738260877398316200197677337735993893876640054030862480179650557345729971470059927578032767319931222828570259113571184368826210270342110464355294248960, 1090748135619415929462984244733782862445058741317256278077723357411872937927833784244419600432340383621359132078539296421583922726078535288895631126147893430149380770045156693316471592314481596094990093519266467060963746463149021913517350803079950400440665964304739215704920738623747423257015752366908264085893021118110308974552597077954159980749712419298225792610335570650809591039390908475045801933904902676564396390725443722970902476505668943463129909442136980589661502329916207474552401367763852856835262959009067319505910523234201508849530123021140590765937850147753368424740552323470408182285922748805210520738945273624250073532547213864411288330003393740150912580166278929704842831018825970092592589997564992748701241134099098189591461277259179911627931227354401824729735222739283906940258565844609867958833251463899830750255317198113101160530620734317932567900498223532817667589142046943165554232191512001478956898687683520250475974324734315380150309747612208712500051022967476984319077129296386777374636865231087169447708549517544139233017684215770290488418789440168334816327372623519038609022141979462139722689427219151234633118646875003741836690327166568052540560892638150017862105394046379266526690121410209850772135746339395758587591648792223654974745634225736271050568271311740257450712934213663479668020824855253157533409992242243185229562856090869187134982573538569852483225539869705077626849803583477586364785204481055628574836838979480433938208897652545831398860133527896735028968302348255129557764568722621963320682441686446392311846397899383114863434253848663932279264188564128386706056453584844520974679854641137384660894775927042925383218566634937141648684602149056050732108371054310349389279475071554719181040574555552962971974792722792653974763290140871652286270098969576677480222940290795746088405409748159994478121367758864292622252744789474675449474741606852764070764063110576030660846709793102667506631035454077016208694602827335899556351637399344567778304083178028820294133459605355876156179714463545661793044235280409193608501261558804583167350441282704397497970403108257267112393653696672675910688099839367469282734578305725116229359673050529813789252273363198230132949795533051518858815503461348243733779388689730783814640911372667854894579549420746122021822981211980082448791461461735149685581518666731366228054655612843460369296145991464644624232666058546546775071466057342070960016482455402459983974533531512623447503628532879196160, 1090748135619415929462984244733782862448264161996232692431832786189721331849109875331513870234605433463932241694048131051358947830205980188196448074959461356758486573232462591433156779577237490627406123547618423722668866652339479999293626021839890161927470072222416275310966999593803517697609822714708579884205550840414698745794222115405131762724689518277473450666725768294443700706103254859716733899036477127355717020008787842924414391583891235738543020558099725138939596081148014590965124539186821561529914566658849262988504621375111628343614858679068075902419555944729073976404444565343555827377610000620947577410278627011740831480055497987845581365988527549373552036103980380460119398337457819050480022405702325635582620236066168807184261870584892432597683277669260204163001806232850994074559052885958077900805983585439963419680319621217850405971289333030803245070840561728370555174569443676693629170452149296065798196661572238035681751946495873207469100150493032277188951439284275065790528306049503847529562489086229780168252138484384622224460015690956455991882709903488025930330456108229822033526376707136090265975193250434767826227728688689631822571110448349847083887734391639427413322727296020796085661840741564416933944834885347677704020625164362236290082483231096646670146316488035415210816619742524561606952935611302947966659440338951555748352481673455328318110092907812432976349828140055049776760942184789064042974347999533186945347522493599199813729152746600124370793863684351800627532861582603373243844541669894180917405990955855670211102417040532303109059148651080538307108200472206951864724440163912445823502524921620535906589683568560322180265439851314707032130422408981737587067461745778054108010454979688805716669890106223718629918609636282362876953861912714996254991032203811132391157099002202347885731138448079694323323449229027719621743895573011766662593894349081522104383894908548239240269319053774558041228754281281816861897527545504098214377454609550129806936928314745701910920161391616609369496032529549582045082542643910019366151847658440920119593061651167368561688293227455295170854030179178723762426736301386023622466277453636011514339531108046811378554467570571147700293987047007133169604516470460363030434395212791168390261169656611459540138630944243057585634982081359365277395087425491626723439059966600654655183801562224994052115182662706659658702893140791266483454391692605083442515414863001025232435847470731267136086799620306370560, 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554717727193825132424258268072070423477350441019325238935081369672808088954075376607323183064685826513719267367765025669297838401423262150842341357600244555889201894556085847866483922724148646867108659100934137092282466892797007055681424336981376513709740535026193493673249209257320971410979203369564857482654510028075971351626483674957465557609650341383284243352703413714646767970869719760282612297099758526022496503350912508240831354915423886988443810272342344732317150627439462977141579914873924393499344568782246440509166066283446893682365040319921619212785451204784909812620149202475072920645750021639932387054565814599265491865025466591172979897528545547657398713095194110513475640015533832552892834462456004562452971528736770337713855531343214788202807563614479213467081621550379582167079624431075961285990652132534019881887236124261807921871717536754538527881569172145267614894322853623609813920928459120198997814593256579843388566344082288016681611654470716138650900737275301237931416801181903989453821932064570156865659395968836640923032250896569702084633936822519618352768176774084397451792927718879958100081887861393908320621408161687515022883010853676704976685223953947630891854814753738450680771222651381548932686869654811143303224385700414066978115266169823947267240120243654344301634559922544942816043553794364709175132165894258852632905428043741747989065584385717223677332433400389608789558933209058517367950612903452919800029473576992005403338790727107551494317528931418468321870206715879080915763252955490226179218331260318126443739420462473525613282748278965996483750636045783491802222016697761633212650864259383149056931239290285624805626122759894380826805436467577805724137767574570906567601847329444596436887515074101490955904440736746378578909097694701009073306364306371857928229086986807866811037349498795349771504573858928341772320617473445645992985275412333509090804871751065163475735116124159825908647121640421907667647356208564338125924147715960797202874727558317522397417637853954101630500329587808124225607721416501990667502342789749660037118355919877562034711995165307625661050344070739613757088494470672876611099532221420366583803436275263239830405586791170387133117796852392016463145034898659808641129024904249424733643211466577601264042611135606503976088487910839773519358050959360, 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554799078906298842192989538609825228048205159696851613591638196771886542609324560121290553901886301017900252535799917200010079600026535836800905297805880952344434142288520078948840015587307354938660586662128298270350249817014271693665765110592008613298778505422237692146259873858659415573867216038413367887863225808775353059030740090896360912642226573857037049962736349533220384817969976483149973107413139227644176078619320341055567499174066505299371568329139777241183089138566334553194650577629094056611619967969653726624148744303488035402293152604489486492100208017863024726771025350917773611238726097375366394777344426511988513556879991178832915713510549481697173215445101845957529458649240419039109240935740910191672068265273719092589036748465496772589128171977093240953165534992672018013618814995161462309538660641385783569275376409313809965475889555022982121273477969648053452876833585167683334003690463172464081216829623878909681066796095037273252169666759578152053991219528513242729480885311699333643283995611022633415058770494955457423321606395672379513094283755488117583208734138564299317466532948220527445976808475956204587074983904100207162912865380688486391072610835612762060729181212793646168221753156439697858063620473480211440842709029593612453629476963272918555621144668718781463666529288238422362202825387580631554852164914519052059660040464663126781487560119934326441860936571324105415002310162950779332518014848112844743427605942506544050522057943770995582957029023526909557365112077631459260712531564908022807631888258826691914906113986248716550085419858013381711311649991056871703624067763554136461504317273126870747233315465647396625310067987550217403326963292546153158772672740041967708838522805761174003091611777775043411335156923698959839678510230832295163313316789267444620224432518792403169045198033711681799380593647401842461843648423716417664365528718045683794601856283379413891052412969460121927658025990683597601528175797008376299141662638078090891860989403913605461823884961828737140171022361679405979038786444181270716007518309822554612689912150227475032388745809549109277022071797772295031123798251651255599727407916691739326020171853970956314931166813991316312725113081108713697206841284865031993483234062808071776305097470274820616405375977422257119466656882704639478857686056960, 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554799078906298842192989538609825228048205159696851613591638196771886542609324560121290553901886301017900252535799917200010079600026535836800905297805880952350501630195475653911005312364560014847426035293551245843928918752768696279344088055617515694349945406677825140814900616105920256438504578013326493565836047242407382442812245131517757519164899226365743722432277368075027627883045206501792761700945699168497257879683851737049996900961120515655050115561271491492481590583927528068362121611832823090350947768974356780606151520143159909137700592185973126172549006476832634892320043175548198813118732027663641737580234180498216659031323755528672469578345747574178638520542422428423677558820978627530386229456967934723788568179648262880758976714398711940255399001607683329891312982140614519561421728861174053416163557141099001227260702498594974247602767107850237371185829184296776123032637607387534110972932388406207584762847633426555552446542114214004891266591088458003495784055858294944168684601688858744297754455478086944868426545830699462053020840665064540392958400443325645527374926882973919246656771539390355706463348469275233864897316857752844929570354333768590343841311070850781091725431885844774325016901949773780261558722409401181833978850211680880235006737620395003207721429913359698783128999341087064869360477360260946612352621282830392338045342868360685801099549739965616135919539306625022788065057280252729962269737132309764754628744321772059641657719823547449320592935611616099240742902136329711517410404030324521840342033994485065200736874265167184988389293259882587602113424959054628993094268364393026247954669688793470940786540624498332650203138482502473546445070830271563685172304095213304349600298515635788989580172037008658825732196098316200861698353829406714272630544531590748563008319858775677970324879375646607814716537093794936528532510075217655406621358266156154358999433998158724863016801311862884415003624026624271858216959376261551815071325789099581359312420237157949795754513740566131017746235944565634476856040075065074597078314422621893894702231993235077806982696786165968173125570545073461288474360408005636640266535246648614607443110206856314723120840607763815821602035459921424929857198102394553285216706183381968298312489240849692137274288006245419386744015437915115941622091612160, 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554799078906298842192989538609825228048205159696851613591638196771886542609324560121290553901886301017900252535799917200010079600026535836800905297805880952350501630195475653911005312364560014847426035293551245843928918752768696279344088055617515694349945406677825140814900616105920256438504578013326493565836047242407382442812245131517757519164899226365743722432277368075027627883045206501792761700945699168497257879683851737049996900961120515655050115561271491492515342105748966629547032786321505730828430221664970324396138635251626409516168005427623435996308921691446181187406395310665404885739434832877428167407495370993511868756359970390117021823616749458620969857006263612082706715408157066575137281027022310927564910276759160520878304632411049364568754920967322982459184763427383790272448438018526977764941072715611580434690827459339991961414242741410599117426060556483763756314527611362658628383368621157993638020878537675545336789915694234433955666315070087213535470255670312004130725495834508357439653828936077080978550578912967907352780054935621561090795845172954115972926435488646325407501512365848213380395168763512806429730109607098577644744240048503459529594006823631373147762011780218660740030215430505248911586325182120160839367048207709418842650690943826010989109302792718425868852384783378651199618535121913835737651699662333815683378345818068070160548347800369481364172406204671458973952634913932812733482191175501628465349005403383205634207163186366050321349674463279843106828789837369958673440743379029655723491233599261110682223445532527992025505094106028374148434683256837486589543018181873279720349434704460879700399438016504650780473547823239120431423814382915239771713285086798751923825359346515261480728322427217167293613096521198247560588729708788376007087530154941809492620352947595475014394229254625965054086766970439573627357949092810593883736061141168581582787315634913260797956280083967967201275577888581524322407185240031043931510925713450658807511908275263101371880394716465807521940885628037330976885109586390268456528362201664202524947917653322271271470730573883899274644538470640093205628124760082118516398285556726512915645798229781241791101398278815512033744564071010914628794915292515492524789530849844709747037539932187090270337487885794730917151571753381797325072561602560]

lemma power_0 : (2 : Nat) ^ (2 ^ 0) = 2 := by
  decide

lemma power_1 : (2 : Nat) ^ (2 ^ 1) = 4 := by
  rw [show (2 : Nat) ^ 1 = 2 ^ 0 * 2 by decide, pow_mul, power_0]
  decide

lemma power_2 : (2 : Nat) ^ (2 ^ 2) = 16 := by
  rw [show (2 : Nat) ^ 2 = 2 ^ 1 * 2 by decide, pow_mul, power_1]
  decide

lemma power_3 : (2 : Nat) ^ (2 ^ 3) = 256 := by
  rw [show (2 : Nat) ^ 3 = 2 ^ 2 * 2 by decide, pow_mul, power_2]
  decide

lemma power_4 : (2 : Nat) ^ (2 ^ 4) = 65536 := by
  rw [show (2 : Nat) ^ 4 = 2 ^ 3 * 2 by decide, pow_mul, power_3]
  decide

lemma power_5 : (2 : Nat) ^ (2 ^ 5) = 4294967296 := by
  rw [show (2 : Nat) ^ 5 = 2 ^ 4 * 2 by decide, pow_mul, power_4]
  decide

lemma power_6 : (2 : Nat) ^ (2 ^ 6) = 18446744073709551616 := by
  rw [show (2 : Nat) ^ 6 = 2 ^ 5 * 2 by decide, pow_mul, power_5]
  decide

lemma power_7 : (2 : Nat) ^ (2 ^ 7) = 340282366920938463463374607431768211456 := by
  rw [show (2 : Nat) ^ 7 = 2 ^ 6 * 2 by decide, pow_mul, power_6]
  decide

lemma power_8 : (2 : Nat) ^ (2 ^ 8) = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  rw [show (2 : Nat) ^ 8 = 2 ^ 7 * 2 by decide, pow_mul, power_7]
  decide

lemma power_9 : (2 : Nat) ^ (2 ^ 9) = 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 := by
  rw [show (2 : Nat) ^ 9 = 2 ^ 8 * 2 by decide, pow_mul, power_8]
  decide

lemma power_10 : (2 : Nat) ^ (2 ^ 10) = 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216 := by
  rw [show (2 : Nat) ^ 10 = 2 ^ 9 * 2 by decide, pow_mul, power_9]
  decide

lemma power_11 : (2 : Nat) ^ (2 ^ 11) = 32317006071311007300714876688669951960444102669715484032130345427524655138867890893197201411522913463688717960921898019494119559150490921095088152386448283120630877367300996091750197750389652106796057638384067568276792218642619756161838094338476170470581645852036305042887575891541065808607552399123930385521914333389668342420684974786564569494856176035326322058077805659331026192708460314150258592864177116725943603718461857357598351152301645904403697613233287231227125684710820209725157101726931323469678542580656697935045997268352998638215525166389437335543602135433229604645318478604952148193555853611059596230656 := by
  rw [show (2 : Nat) ^ 11 = 2 ^ 10 * 2 by decide, pow_mul, power_10]
  decide

lemma power_12 : (2 : Nat) ^ (2 ^ 12) = 1044388881413152506691752710716624382579964249047383780384233483283953907971557456848826811934997558340890106714439262837987573438185793607263236087851365277945956976543709998340361590134383718314428070011855946226376318839397712745672334684344586617496807908705803704071284048740118609114467977783598029006686938976881787785946905630190260940599579453432823469303026696443059025015972399867714215541693835559885291486318237914434496734087811872639496475100189041349008417061675093668333850551032972088269550769983616369411933015213796825837188091833656751221318492846368125550225998300412344784862595674492194617023806505913245610825731835380087608622102834270197698202313169017678006675195485079921636419370285375124784014907159135459982790513399611551794271106831134090584272884279791554849782954323534517065223269061394905987693002122963395687782878948440616007412945674919823050571642377154816321380631045902916136926708342856440730447899971901781465763473223850267253059899795996090799469201774624817718449867455659250178329070473119433165550807568221846571746373296884912819520317457002440926616910874148385078411929804522981857338977648103126085903001302413467189726673216491511131602920781738033436090243804708340403154190336 := by
  rw [show (2 : Nat) ^ 12 = 2 ^ 11 * 2 by decide, pow_mul, power_11]
  decide

lemma power_13 : (2 : Nat) ^ (2 ^ 13) = 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554799078906298842192989538609825228048205159696851613591638196771886542609324560121290553901886301017900252535799917200010079600026535836800905297805880952350501630195475653911005312364560014847426035293551245843928918752768696279344088055617515694349945406677825140814900616105920256438504578013326493565836047242407382442812245131517757519164899226365743722432277368075027627883045206501792761700945699168497257879683851737049996900961120515655050115561271491492515342105748966629547032786321505730828430221664970324396138635251626409516168005427623435996308921691446181187406395310665404885739434832877428167407495370993511868756359970390117021823616749458620969857006263612082706715408157066575137281027022310927564910276759160520878304632411049364568754920967322982459184763427383790272448438018526977764941072715611580434690827459339991961414242741410599117426060556483763756314527611362658628383368621157993638020878537675545336789915694234433955666315070087213535470255670312004130725495834508357439653828936077080978550578912967907352780054935621561090795845172954115972927479877527738560008204118558930004777748727761853813510493840581861598652211605960308356405941821189714037868726219481498727603653616298856174822413033485438785324024751419417183012281078209729303537372804574372095228703622776363945290869806258422355148507571039619387449629866808188769662815778153079393179093143648340761738581819563002994422790754955061288818308430079648693232179158765918035565216157115402992120276155607873107937477466841528362987708699450152031231862594203085693838944657061346236704234026821102958954951197087076546186622796294536451620756509351018906023773821539532776208676978589731966330308893304665169436185078350641568336944530051437491311298834367265238595404904273455928723949525227184617404367854754610474377019768025576605881038077270707717942221977090385438585844095492116099852538903974655703943973086090930596963360767529964938414598185705963754561497355827813623833288906309004288017321424808663962671333528009232758350873059614118723781422101460198615747386855096896089189180441339558524822867541113212638793675567650340362970031930023397828465318547238244232028015189689660418822976000815437610652254270163595650875433851147123214227266605403581781469090806576468950587661997186505665475715792896 := by
  rw [show (2 : Nat) ^ 13 = 2 ^ 12 * 2 by decide, pow_mul, power_12]
  decide

lemma col_1_0 : PackedColumns.col 1 0 = 2 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_0]
  decide

lemma col_2_0 : PackedColumns.col 2 0 = 10 := by
  rw [PackedColumns.col]
  simp only [show 0 < 1 by decide, ↓reduceIte]
  simp only [col_1_0]
  decide

lemma col_2_1 : PackedColumns.col 2 1 = 12 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_1]
  decide

lemma col_3_0 : PackedColumns.col 3 0 = 170 := by
  rw [PackedColumns.col]
  simp only [show 0 < 2 by decide, ↓reduceIte]
  simp only [col_2_0]
  decide

lemma col_3_1 : PackedColumns.col 3 1 = 204 := by
  rw [PackedColumns.col]
  simp only [show 1 < 2 by decide, ↓reduceIte]
  simp only [col_2_1]
  decide

lemma col_3_2 : PackedColumns.col 3 2 = 240 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_2]
  decide

lemma col_4_0 : PackedColumns.col 4 0 = 43690 := by
  rw [PackedColumns.col]
  simp only [show 0 < 3 by decide, ↓reduceIte]
  simp only [col_3_0]
  decide

lemma col_4_1 : PackedColumns.col 4 1 = 52428 := by
  rw [PackedColumns.col]
  simp only [show 1 < 3 by decide, ↓reduceIte]
  simp only [col_3_1]
  decide

lemma col_4_2 : PackedColumns.col 4 2 = 61680 := by
  rw [PackedColumns.col]
  simp only [show 2 < 3 by decide, ↓reduceIte]
  simp only [col_3_2]
  decide

lemma col_4_3 : PackedColumns.col 4 3 = 65280 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_3]
  decide

lemma col_5_0 : PackedColumns.col 5 0 = 2863311530 := by
  rw [PackedColumns.col]
  simp only [show 0 < 4 by decide, ↓reduceIte]
  simp only [col_4_0]
  decide

lemma col_5_1 : PackedColumns.col 5 1 = 3435973836 := by
  rw [PackedColumns.col]
  simp only [show 1 < 4 by decide, ↓reduceIte]
  simp only [col_4_1]
  decide

lemma col_5_2 : PackedColumns.col 5 2 = 4042322160 := by
  rw [PackedColumns.col]
  simp only [show 2 < 4 by decide, ↓reduceIte]
  simp only [col_4_2]
  decide

lemma col_5_3 : PackedColumns.col 5 3 = 4278255360 := by
  rw [PackedColumns.col]
  simp only [show 3 < 4 by decide, ↓reduceIte]
  simp only [col_4_3]
  decide

lemma col_5_4 : PackedColumns.col 5 4 = 4294901760 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_4]
  decide

lemma col_6_0 : PackedColumns.col 6 0 = 12297829382473034410 := by
  rw [PackedColumns.col]
  simp only [show 0 < 5 by decide, ↓reduceIte]
  simp only [col_5_0]
  decide

lemma col_6_1 : PackedColumns.col 6 1 = 14757395258967641292 := by
  rw [PackedColumns.col]
  simp only [show 1 < 5 by decide, ↓reduceIte]
  simp only [col_5_1]
  decide

lemma col_6_2 : PackedColumns.col 6 2 = 17361641481138401520 := by
  rw [PackedColumns.col]
  simp only [show 2 < 5 by decide, ↓reduceIte]
  simp only [col_5_2]
  decide

lemma col_6_3 : PackedColumns.col 6 3 = 18374966859414961920 := by
  rw [PackedColumns.col]
  simp only [show 3 < 5 by decide, ↓reduceIte]
  simp only [col_5_3]
  decide

lemma col_6_4 : PackedColumns.col 6 4 = 18446462603027742720 := by
  rw [PackedColumns.col]
  simp only [show 4 < 5 by decide, ↓reduceIte]
  simp only [col_5_4]
  decide

lemma col_6_5 : PackedColumns.col 6 5 = 18446744069414584320 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_5]
  decide

lemma col_7_0 : PackedColumns.col 7 0 = 226854911280625642308916404954512140970 := by
  rw [PackedColumns.col]
  simp only [show 0 < 6 by decide, ↓reduceIte]
  simp only [col_6_0]
  decide

lemma col_7_1 : PackedColumns.col 7 1 = 272225893536750770770699685945414569164 := by
  rw [PackedColumns.col]
  simp only [show 1 < 6 by decide, ↓reduceIte]
  simp only [col_6_1]
  decide

lemma col_7_2 : PackedColumns.col 7 2 = 320265757102059730318470218759311257840 := by
  rw [PackedColumns.col]
  simp only [show 2 < 6 by decide, ↓reduceIte]
  simp only [col_6_2]
  decide

lemma col_7_3 : PackedColumns.col 7 3 = 338958311018522360492699998064329424640 := by
  rw [PackedColumns.col]
  simp only [show 3 < 6 by decide, ↓reduceIte]
  simp only [col_6_3]
  decide

lemma col_7_4 : PackedColumns.col 7 4 = 340277174703306882242637262502835978240 := by
  rw [PackedColumns.col]
  simp only [show 4 < 6 by decide, ↓reduceIte]
  simp only [col_6_4]
  decide

lemma col_7_5 : PackedColumns.col 7 5 = 340282366841710300967557013907638845440 := by
  rw [PackedColumns.col]
  simp only [show 5 < 6 by decide, ↓reduceIte]
  simp only [col_6_5]
  decide

lemma col_7_6 : PackedColumns.col 7 6 = 340282366920938463444927863358058659840 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_6]
  decide

lemma col_8_0 : PackedColumns.col 8 0 = 77194726158210796949047323339125271902179989777093709359638389338608753093290 := by
  rw [PackedColumns.col]
  simp only [show 0 < 7 by decide, ↓reduceIte]
  simp only [col_7_0]
  decide

lemma col_8_1 : PackedColumns.col 8 1 = 92633671389852956338856788006950326282615987732512451231566067206330503711948 := by
  rw [PackedColumns.col]
  simp only [show 1 < 7 by decide, ↓reduceIte]
  simp only [col_7_1]
  decide

lemma col_8_2 : PackedColumns.col 8 2 = 108980789870415242751596221184647442685430573802955824978313020242741769072880 := by
  rw [PackedColumns.col]
  simp only [show 2 < 7 by decide, ↓reduceIte]
  simp only [col_7_2]
  decide

lemma col_8_3 : PackedColumns.col 8 3 = 115341536360906404779899502576747487978354537254490211650198994186870666100480 := by
  rw [PackedColumns.col]
  simp only [show 3 < 7 by decide, ↓reduceIte]
  simp only [col_7_3]
  decide

lemma col_8_4 : PackedColumns.col 8 4 = 115790322417210952336529717160220497262186272106556906860092653394915770695680 := by
  rw [PackedColumns.col]
  simp only [show 4 < 7 by decide, ↓reduceIte]
  simp only [col_7_4]
  decide

lemma col_8_5 : PackedColumns.col 8 5 = 115792089210356248762697446947946071893095522863849111501270640965525260206080 := by
  rw [PackedColumns.col]
  simp only [show 5 < 7 by decide, ↓reduceIte]
  simp only [col_7_5]
  decide

lemma col_8_6 : PackedColumns.col 8 6 = 115792089237316195417293883273301227089774477609353836086800156426807153786880 := by
  rw [PackedColumns.col]
  simp only [show 6 < 7 by decide, ↓reduceIte]
  simp only [col_7_6]
  decide

lemma col_8_7 : PackedColumns.col 8 7 = 115792089237316195423570985008687907852929702298719625575994209400481361428480 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_7]
  decide

lemma col_9_0 : PackedColumns.col 9 0 = 8938538619961731399716016665470564084986243880394928918482374295814509353382364651201249532111268951793354572124324033902502588541297713297622432670722730 := by
  rw [PackedColumns.col]
  simp only [show 0 < 8 by decide, ↓reduceIte]
  simp only [col_8_0]
  decide

lemma col_9_1 : PackedColumns.col 9 1 = 10726246343954077679659219998564676901983492656473914702178849154977411224058837581441499438533522742152025486549188840683003106249557255957146919204867276 := by
  rw [PackedColumns.col]
  simp only [show 1 < 8 by decide, ↓reduceIte]
  simp only [col_8_1]
  decide

lemma col_9_2 : PackedColumns.col 9 2 = 12619113345828326681952023527723149296451167831145782002563351947032248498892750095813528751215909108414147631234339812568238948528890889361349316711608560 := by
  rw [PackedColumns.col]
  simp only [show 2 < 8 by decide, ↓reduceIte]
  simp only [col_8_2]
  decide

lemma col_9_3 : PackedColumns.col 9 3 = 13355637471071225126423931515722554897411352724014212858744092333045803858750303603351283347590378511628981150567083381395178964979993470452478654262869760 := by
  rw [PackedColumns.col]
  simp only [show 3 < 8 by decide, ↓reduceIte]
  simp only [col_8_3]
  decide

lemma col_9_4 : PackedColumns.col 9 4 = 13407603346151304507647333602124270744930157291580986197148043437687863763597662002711256755796972443613438635551055889478487182262900810351549134401372160 := by
  rw [PackedColumns.col]
  simp only [show 4 < 8 by decide, ↓reduceIte]
  simp only [col_8_4]
  decide

lemma col_9_5 : PackedColumns.col 9 5 = 13407807926820848549984871490950625460264621687587329935306297008442977448960781863686381587396241115434734742314166555940848600484775015044616064818216960 := by
  rw [PackedColumns.col]
  simp only [show 5 < 8 by decide, ↓reduceIte]
  simp only [col_8_5]
  decide

lemma col_9_6 : PackedColumns.col 9 6 = 13407807929942597098847186273910239236969444018900783322580063136098668673514857287274768220802268387129003177701362428774192761570871467260109520434626560 := by
  rw [PackedColumns.col]
  simp only [show 6 < 8 by decide, ↓reduceIte]
  simp only [col_8_6]
  decide

lemma col_9_7 : PackedColumns.col 9 7 = 13407807929942597099574024998205846127439963814395998898511282403621620416268583029620646167694378705270794824322841769944638336182637648515027502377205760 := by
  rw [PackedColumns.col]
  simp only [show 7 < 8 by decide, ↓reduceIte]
  simp only [col_8_7]
  decide

lemma col_9_8 : PackedColumns.col 9 8 = 13407807929942597099574024998205846127479365820592393377723561443721764030073431184712636981971479856705023170278632780869088242247907112362425735876444160 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_8]
  decide

lemma col_10_0 : PackedColumns.col 10 0 = 119846208990821060515287012719268315574531798596153771515620054105155117203667308755138984881605024014080075919914262238439193179209611081661898287092982749585178595616576990184201479734164062746302055301390003845892100454894975254315942073693884824775567007123057532159964830625653144203223570886416149424810 := by
  rw [PackedColumns.col]
  simp only [show 0 < 9 by decide, ↓reduceIte]
  simp only [col_9_0]
  decide

lemma col_10_1 : PackedColumns.col 10 1 = 143815450788985272618344415263121978689438158315384525818744064926186140644400770506166781857926028816896091103897114686127031815051533297994277944511579299502214314739892388221041775680996875295562466361668004615070520545873970305179130488432661789730680408547669038591957796750783773043868285063699379309772 := by
  rw [PackedColumns.col]
  simp only [show 1 < 9 by decide, ↓reduceIte]
  simp only [col_9_1]
  decide

lemma col_10_2 : PackedColumns.col 10 2 = 169194647987041497198052253250731739634633127429864148022051841089630753699295024124902096303442386843407166004584840807208272723590039174110915228837152117061428605576343986142402089036466912112426431013727064253024141818675259182563682927567837399683153421820787104225832702059745615345727394192587505070320 := by
  rw [PackedColumns.col]
  simp only [show 2 < 9 by decide, ↓reduceIte]
  simp only [col_9_2]
  decide

lemma col_10_3 : PackedColumns.col 10 3 = 179069821994067265517004719393770557123035839147560499073922571114317373565012632536861362624654977515201358572945823733699027940920197102560968646862666832065013932750060561209079253766221790251284004808302573839776523636885877422791135238515376547524582609864801915756523326693582908070186191519003118206720 := by
  rw [PackedColumns.col]
  simp only [show 3 < 9 by decide, ↓reduceIte]
  simp only [col_9_3]
  decide

lemma col_10_4 : PackedColumns.col 10 4 = 179766570466052360237648572536963127610949142151705149077185617265867657072940646045213890928808158455225716514812268414598264282604049739409665520460023745597470080465874001603182053859457467143941243028332742390810947146161643764595180884270010128854499581430719252352917935056902309958553029775825154539520 := by
  rw [PackedColumns.col]
  simp only [show 4 < 9 by decide, ↓reduceIte]
  simp only [col_9_4]
  decide

lemma col_10_5 : PackedColumns.col 10 5 = 179769313444375785814462265863485611229889718115776549548420631039577310219318555512504201030636628662239812719543346771400604958784932998973090366819193438631844709885019339289485527600645229101680144570744617427323613239093066544488844122372018577072445227788470567772585250041087614243742592599359351685120 := by
  rw [PackedColumns.col]
  simp only [show 5 < 9 by decide, ↓reduceIte]
  simp only [col_9_5]
  decide

lemma col_10_6 : PackedColumns.col 10 6 = 179769313486231590763185205067502474281972610037491134208877555181135709923949037735690276024213413705823039792595812100825199281213020878487102478859428781160318831728534053767098825058678708531551206723464342007537350133167915838047987720003371153224504147359993809275143228500884134199151686065190149816320 := by
  rw [PackedColumns.col]
  simp only [show 6 < 9 by decide, ↓reduceIte]
  simp only [col_9_6]
  decide

lemma col_10_7 : PackedColumns.col 10 7 = 179769313486231590772930519078902473361269403363094992027077741372816159198983668324764656509214724291581902479869920821760871587342679845464593386307578492764517105656857966598509267284159204378328176331317696638943488431251920295735812264550083217605459765810970935573515804682568218669795142748890432798720 := by
  rw [PackedColumns.col]
  simp only [show 7 < 9 by decide, ↓reduceIte]
  simp only [col_9_7]
  decide

lemma col_10_8 : PackedColumns.col 10 8 = 179769313486231590772930519078902473361797697894230657273430081157732675805499410614616176613472387041631651377316136471641673072203277570454821379686787760899244944958633938372376730076395090525612731964434268678008150116831451773765893368201788358737656950422124978427902852027528247743196825908506284523520 := by
  rw [PackedColumns.col]
  simp only [show 8 < 9 by decide, ↓reduceIte]
  simp only [col_9_8]
  decide

lemma col_10_9 : PackedColumns.col 10 9 = 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474110969959963482268385702277221395399966640087262359691628045276706960578432807926936308666529070259922820652728111753896392184596904358265409895975218053120 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_9]
  decide

lemma col_11_0 : PackedColumns.col 11 0 = 21544670714207338200476584459113301306962735113143656021420230285016436759245260595464800941015275642459145307281265346329413039433660614063392101590965522080420584911533997394500131833593101404530705092256045045517861479095079837441225396225650780313721097234690870028591717261027377205738368266082620257014609555593112228280456649857709712996570784023550881372051870439554017461805640209433505728576118077817295735812307904905065567434867763936269131742155524820818083789807213473150104734484620882313119028387104465290030664845568665758810350110926291557029068090288819736430212319069968098795703902407373064153770 := by
  rw [PackedColumns.col]
  simp only [show 0 < 10 by decide, ↓reduceIte]
  simp only [col_10_0]
  decide

lemma col_11_1 : PackedColumns.col 11 1 = 25853604857048805840571901350935961568355282135772387225704276342019724111094312714557761129218330770950974368737518415595295647320392736876070521909158626496504701893840796873400158200311721685436846110707254054621433774914095804929470475470780936376465316681629044034310060713232852646886041919299144308417531466711734673936547979829251655595884940828261057646462244527464820954166768251320206874291341693380754882974769485886078680921841316723522958090586629784981700547768656167780125681381545058775742834064525358348036797814682398910572420133111549868434881708346583683716254782883961718554844682888847676984524 := by
  rw [PackedColumns.col]
  simp only [show 1 < 10 by decide, ↓reduceIte]
  simp only [col_10_1]
  decide

lemma col_11_2 : PackedColumns.col 11 2 = 30416005714175065694790472177571719492182684865614573206710913343552616601287426723009130740256859730530558080867668724229759585082814984560082966951951325290005531639812702204000186118013790218160995424361475358378157382251877417564082912318565807501723901978387110628600071427332767819865931669763699186373566431425570204631232917446178418348099930386189479584073228855840965828431492060376713969754519639271476332911493512807151389319813313792379950694807799747037294762080771962094265507507700069147932745958265127468278585664332234012438141333072411609923390245113627863195593862216425551240993744575114914099440 := by
  rw [PackedColumns.col]
  simp only [show 2 < 10 by decide, ↓reduceIte]
  simp only [col_10_2]
  decide

lemma col_11_3 : PackedColumns.col 11 3 = 32191258965975166805381355767702364598730312386953945183756297390841679827043502212678924363229049987176310498038933435760679405223835314398220105100897900696036982902836789881276461572372571748403855079479849406532524544640119290184554677628987936344236970187242389459063110615698493568107133907298545442387587818473755236029943009904126575061024050836745285785478281123691605857328271752616599999117623898372924367906327764527413143560269343780262048984388021522156203016676925967663969720008149489526216758368280601834131421403495593974253597052901540692214638702999637271553313348338006809095526453402456251498240 := by
  rw [PackedColumns.col]
  simp only [show 3 < 10 by decide, ↓reduceIte]
  simp only [col_10_3]
  decide

lemma col_11_4 : PackedColumns.col 11 4 = 32316512960456508147453349385365121560029673505996215291052295923497502161845157660200677353335759292556934560431168784130592175847026458411091401113848279332188918918220823044523566226246795557791574734716850819454473882554323944334074207708109530615683335254269363676864674514061298027570754749667911282871724029983449112545310443072040154819642253271451940772360453967833714276902233168258408946731567076945106428632575740174062980318251379617483264824158211574922576695198259201131389838088044481970625035728915228891636395882917773452463381865274549723395723172372127735020455495580422417626880638757562929315840 := by
  rw [PackedColumns.col]
  simp only [show 4 < 10 by decide, ↓reduceIte]
  simp only [col_10_4]
  decide

lemma col_11_5 : PackedColumns.col 11 5 = 32317006063786617977917430647786889867906369439928774745874403061933612682200576450810216481426203250827948543126557362463291876111646222960360790085163651852238641429717120847798370265322261673906889097924268663692940257295126353200399956021066277899174676540581348497257723324380162489733907944315511759482739072698058393384635692285896212301876001058488500506831120565403102471120452564365415396618005887063102909747528554645081362840155633503159179847489820241277356288078525972093195870585301724764277428214574822136154041715694457110709920357539707654728889907475699213364849177130473778351627777064507057111040 := by
  rw [PackedColumns.col]
  simp only [show 5 < 10 by decide, ↓reduceIte]
  simp only [col_10_5]
  decide

lemma col_11_6 : PackedColumns.col 11 6 = 32317006071311007298962968279132820423318564169544585575840362784271006144270719271112334871465990491032121249854708136351097131222229533897039842809000575024469795858601452903608286950487291036173656424642694699111215656720330692156806652878176294560992911131049744850351554674082581482982160517647675979048835286736621524221873911053756802868040397366267058518789526418606983189736261563041441886139662520217871559010598356884184331324030205339382405674779699808810844071987274263786247133048684130104820097246644482379610721840409187043258179179795737779347699068638486420172878212978512006155262375419323025981440 := by
  rw [PackedColumns.col]
  simp only [show 6 < 10 by decide, ↓reduceIte]
  simp only [col_10_6]
  decide

lemma col_11_7 : PackedColumns.col 11 7 = 32317006071311007300714876688669951960349131524534694890724875563828770168877477517674144147156520330032050859708107053367541780354298485118594865664828671846811824087147165337278333530998363043786544832224103197459486604404605511324149101655290064231896878300552753692653117794267740933710191915457110569482353408144600202632326067708533016730171645788373932339760925266412651919717201339056200596183833289262707915216292923080049316321410249206727677420171938451885976792643871821700059247191423513203065085185628574928209860250798213758159017512799345696238071622024309939738578610163879497403419196726710621962240 := by
  rw [PackedColumns.col]
  simp only [show 7 < 10 by decide, ↓reduceIte]
  simp only [col_10_7]
  decide

lemma col_11_8 : PackedColumns.col 11 8 = 32317006071311007300714876688669951960444102669715484032130345427524655138867611798085573559146505641014799895848992131558773898897874931575600122725169680536153603186965708812344954253910382450831936435667181350651846563501034918154134916228896586215374039929970959986026631115266885080258995661844475996688216120407152368914262326688954297921116905358475567711539686747169438627081137712541397537050050280114428159335126130122919957080213913170378129944336867880090300295888143939010064438356220959263775585323618856951444769654532129484978655322733173025761463008789789037153537230130181217227468995996591943843840 := by
  rw [PackedColumns.col]
  simp only [show 8 < 10 by decide, ↓reduceIte]
  simp only [col_10_8]
  decide

lemma col_11_9 : PackedColumns.col 11 9 = 32317006071311007300714876688669951960444102669715484032130345427524655138867890893197201411522913463688717960921898019494119559150490921095088152386448280710318450446268407511633591722075539194702809692695116208601753153385228164358637425253452063124531982403270024154882788029124087013649227429510942494747442647489815192386233134523565554286718296887677415327531178143142900963914851815895844970678619654931422375297655621241901859303687650732732577258002390973227976426601145541195422760363881209530177954039354611088039227582300249931078656601680784145297277963248059010428202344946224651318834406502274474967040 := by
  rw [PackedColumns.col]
  simp only [show 9 < 10 by decide, ↓reduceIte]
  simp only [col_10_9]
  decide

lemma col_11_10 : PackedColumns.col 11 10 = 32317006071311007300714876688669951960444102669715484032130345427524655138867890893197201411522913463688717960921898019494119559150490921095088152386448283120630877367300996091750197750389652106796057638384067568276792218642619756161838094338476170470581645852036305042887575891541065808607552399123930385521734564076182110829912044267485667021494378337432091400804375578173293516902959351017550115541769580704823489838590463999939561383487229281910850182593813106849357791285954724448854882125685229350225459628571692166207846586010535756741612055848610098380251624748643306405371232666472431888720497281435372093440 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_10]
  decide

lemma col_12_0 : PackedColumns.col 12 0 = 696259254275435004461168473811082921719976166031589186922822322189302605314371637899217874623331705560593404476292841891991715625457195738175490725234243518630637984362473332226907726756255812209618713341237297484250879226265141830448223122896391078331205272470535802714189365826745739409645318522398686004457959317921191857297937086793507293733052968955215646202017797628706016677314933245142810361129223706590194324212158609622997822725207915092997650066792694232672278041116729112222567034021981392179700513322410912941288676809197883891458727889104500814212328564245417033483998866941563189908397116328129744682537670608830407217154556920058405748068556180131798801542112678452004450130323386614424279580190250083189343271439423639988527008933074367862847404554089393722848589519861036566521969549023011376815512707596603991795334748642263791855252632293744004941963783279882033714428251436544214253754030601944091284472228570960486965266647934520977175648815900178168706599863997393866312801183083211812299911637106166785552713648746288777033871712147897714497582197923275213013544971334960617744607249432256718941286536348654571559318432068750723935334201608978126484448810994340754401947187825355624060162536472226935436126890 := by
  rw [PackedColumns.col]
  simp only [show 0 < 11 by decide, ↓reduceIte]
  simp only [col_11_0]
  decide

lemma col_12_1 : PackedColumns.col 12 1 = 835511105130522005353402168573299506063971399237907024307386786627163126377245965479061449547998046672712085371551410270390058750548634885810588870281092222356765581234967998672289272107506974651542456009484756981101055071518170196537867747475669293997446326964642963257027238992094887291574382226878423205349551181505430228757524504152208752479663562746258775442421357154447220012777919894171372433355068447908233189054590331547597387270249498111597180080151233079206733649340074934667080440826377670615640615986893095529546412171037460669750473466925400977054794277094500440180798640329875827890076539593755693619045204730596488660585468304070086897682267416158158561850535214142405340156388063937309135496228300099827211925727308367986232410719689241435416885464907272467418307423833243879826363458827613652178615249115924790154401698370716550226303158752492805930356539935858440457313901723853057104504836722332909541366674285152584358319977521425172610778579080213802447919836796872639575361419699854174759893964527400142663256378495546532440646054577477257397098637507930255616253965601952741293528699318708062729543843618385485871182118482500868722401041930773751781338573193208905282336625390426748872195043766672322523352268 := by
  rw [PackedColumns.col]
  simp only [show 1 < 11 by decide, ↓reduceIte]
  simp only [col_11_1]
  decide

lemma col_12_2 : PackedColumns.col 12 2 = 982954241330025888651061374792117065957613410868125910949866807796662501620289371151836999468232996085543629848884012082811833824174864571541869259154226143949135977923491763143869731891184676060638183540570302330707123613550788466515138526441963875291113325840756427361208516461288102695969861443386380241587707272359329680891205299002598532329015956172069147579319243711114376485621082228436908745123609938715568457711282742997173396788528821307761388329589685975537333705105970511373035812736914906606636018808109524152407543730632306670294674666971059973005640325993529929624468988623383326929501811286771404257700240859525280777159374475376572820802667548421363013941806134285182753125162428161540159407327411882149661089090951021160273424376104989924019865252832085255786244028039110446854545245679545473151312057783440929593413762789078294383886069120579771682772399924539341714486943204533008358240984379215187695725499159003040421552914731088438365621857741428002879905690349261928912189905529240205599875252385176638427360445288878273459583593620561479290704279421094418372063488943473813286504352139656544387698639551041748083743668802942198496942402271498531507457144933186947390984265165207939849641227960790967674532080 := by
  rw [PackedColumns.col]
  simp only [show 2 < 11 by decide, ↓reduceIte]
  simp only [col_11_2]
  decide

lemma col_12_3 : PackedColumns.col 12 3 = 1040325111446564364642368458923952692375372948467432870732932963893743970586454120440854723172604571732559795015161289052625754086286237990114351900739103156241887105039648869942150066437362769994138466626595806357791196976209394797245594082459977331047403986882045713004858818978483906355267713278603484146738740770746060985223376814508586773515534397193785245687061612021101596903069783525816494858652225304788461558355910140448370287651672526831560691150382858308739901820189976572348115723986151185202354074380567278480369073520357927682179577857650304718511806103775253466372978851772608034726943551245143276101534885267668779655203695942811003141082978883932337508918954352239570851556592141867466627855225898956983298895847232209165736853814399055483787561668367031866046141539403260862040608197762009216720454784891423863227270597193110101449093427240457968473595691748928797456577620823474623632068279187340587755787298720812556399464563450801771344160098465635862970172559435794726319516164606822318767183146493260878024288097737645487863839445388298530611173400788084364969654743161964502777934567245083969157408676878923562174234544414008863778865110575282492490382659228898247822364669746834862408958809359280712869543680 := by
  rw [PackedColumns.col]
  simp only [show 3 < 11 by decide, ↓reduceIte]
  simp only [col_11_3]
  decide

lemma col_12_4 : PackedColumns.col 12 4 = 1044372945546673828197059762417026954800502571456876931065827327471461972821825678502902390206631368287052718825052894233034066448646477102180500179340327980460903556994805658654408001145108432846397576884767250437032492049663068228640037320493871073809768575078864634481524503993658744936841378031125630239135682634068157595553907065934494117874392161071967268630592757954931050604189499026969785460738929265188251870658590413970416374951231195893953659645177365668990274509878983454352918652249826186380720497759224291404556847049016414820116251680890624350219398922434372584335734388449630404515847080634152714058809270664364623816701429169315371754247697433994176562656146066230462875407957492679621654635564983813385495231023408174091462213500113564221574854773413548995695679450698374027425358111405131610944537607879160761240956820277539402086435979141617874815978878367113591440913603448709010757297957250003996973141247805662445803646376223433329878923069384486850123343958838515748874889108470208492856409563667617066496390779656608815440708680455115994414915549760435273816066113220195745407416742423189412069582551371258052742225599983009157662680521765857237071078259853024604738224458732986851207870637736939387843706880 := by
  rw [PackedColumns.col]
  simp only [show 4 < 11 by decide, ↓reduceIte]
  simp only [col_11_4]
  decide

lemma col_12_5 : PackedColumns.col 12 5 = 1044388881169986771263999928297300478070936649208137728716943272393150591271948624420606938378920325202647294538519193960583205430494401530480726046945869627125087576581441327184118791310492792158585976224097806280786892334766443875874066521728508219835242054530032570439342984842587365877130096578662750128451040500682764243793544319987273001483203699431458496061689471587577966752850769161623090706823127685972966430520428544916906687945372820189637536712212655530164534640139529398430844193326157970231116707311043062974574041904731135129602518839900824182031247902924614891437360369084692512773049940085501258098285770563207273639006194329011676441358313778892352118743746625795899402033165894235998571329265373996173471467022665683468183571100746705885850316405201516404038307610261005853895790796714546886639039188218465580120113917176202211286567528963263244593849404764230833283608612046582861144620238070068732151016953715065309433503193260162865354888677237019030264347447682156758356038253494239532670303481845396141046688302205997576446382970422445081164582128534982238690352916408567003808683045489108822658780334520875388558807595660704043381189270580666647121408487807204873312099823339727666234219348909033811901153280 := by
  rw [PackedColumns.col]
  simp only [show 5 < 11 by decide, ↓reduceIte]
  simp only [col_11_5]
  decide

lemma col_12_6 : PackedColumns.col 12 6 = 1044388881413152506635136276009232092089202823436447410265032820226910016431650373821674532042254867838139147378579230266491649995086065497860958814445672983098674523922997302141987634666555615082983722320304956269495278966036628895198106523331321502350737542153318103393882108000571554757684726905909324459997731583883472732858966036228952156530271920897101714520128973521712735784643100820956652071166631477054434832397108876846187098344767158469121788585996206841660890750835750693609949169201177900602307658491760075332453005821036069979320207117722662159235830901138134661393429664477233482343753829841470905483136731221333733877769217174834552514251616968573563993492617495295314148382180608135581157273932514282997974199539452706406993951290912724329624341760460719763633771633144874653690249377653301500883009114539659231880768729006104695088072439311612787369829426929753368862093420031376900651804074900837670263910502048479989177994719261381762582742114295637847119814372497857489551334050635355850952294274817187604959104441222319544162008246019080907519047450074089096679813611777251441599542273895187986028643056257369619265109472987219292553483853374985528466622647542440199749314968114021310984993945131021102041006080 := by
  rw [PackedColumns.col]
  simp only [show 6 < 11 by decide, ↓reduceIte]
  simp only [col_11_6]
  decide

lemma col_12_7 : PackedColumns.col 12 7 = 1044388881413152506691752710716624382576895065971976858589353558325762581703586392634626505372588775243352352872105555185162748037255922495907952398447320058874700219096305073257981830242798435018035019686250651065418447415300338976514028339919790540980387792506834595479320761864581409260493792716549666612049159545942355726765079667777658031392208221100212494804933965627458645374255563389838434653801141053202689771772723357135216290338695574272496666981821274149184005607430785375049614222602832045450996628806886507199929541770466891583529548235274898663973127724463951951808300980838223831519578183355159780297410327421594977202888369167777179438592323739958538795846107460850234988177201145750964409766625686468495075918326548817949557684257813730076538763495642113203681518969810948925707607978938570829087460191619207747778301032821196208427179851985730907623422392806420997835744218954081402941621610986598423511742048440577277941329354904592254225541145045407068107116812699371822895596907372297376022604084695037964149568827092433282418334219228004804244213575376376596603956419390270373352068036894356733923812512845494539668164417753658652817480459690527778339054327242899088717363700792681812630673715267993584984391680 := by
  rw [PackedColumns.col]
  simp only [show 7 < 11 by decide, ↓reduceIte]
  simp only [col_11_7]
  decide

lemma col_12_8 : PackedColumns.col 12 8 = 1044388881413152506691752710716624382579964249047383780384233483283953907971548437330409861406439184862803595481780311363145047917784297492335081783587410389201085291003814724679247064006671965573116422575979128538114100332241674615061933189180684714263835399074900879577540164624257737073754377690779747879247076068708297591543861086689922251656106269806526857140849097848020246865224175226804081438728633403210458335090491660415105742009535386950924884328661026761230353637743702090864583446899967829903677272414380179127411591801030617544226984469391350202964315137212226053642808605295196669336567154773082816496671483611706639790862104308694690915303767542225100781954758506791181210226942698767971330918318987522521788982684753862563089534063043478107744494626356398106199729676496226503074872846326045491459111066027723006347168934171097334117299464743656642561004725739279259315461208549110360886408197976252866883289138591398644610234775266782248621442697914105954021224136874892190232353067578327032607013349675284007976635788833539884684616422541182911816223459033073906897174276429338970188739690807348257688010677971263071629760560585335781557762874848132251630064790978167461342051030462977170181956787177465479828602880 := by
  rw [PackedColumns.col]
  simp only [show 8 < 11 by decide, ↓reduceIte]
  simp only [col_11_8]
  decide

lemma col_12_9 : PackedColumns.col 12 9 = 1044388881413152506691752710716624382579964249047383780384233483283953907971557456848826811934997558340890106714439262837987573438185793607263236087851365200051875641980331233831654138225785083950552277465749725235095346794307599601916087333516532942974033504539897429691338256245201060803893914535756384924762851404239611614608500917109405562380204866454265949087291595759606743764877742468162792104667105495459173531264931375171503341077321717949680998881907145818504688483711045395643582170427950798206975128373353831495314746178286730941650689781849877290214668035731179963609644181307854096174130583818979052166921580848728037242695212949929951551042190561929025086448680160504932230311456540897613584640906445984196552467049924272345293647753175864255808082351549504606730041888017823936400114385158144513058535899526249634545253015374794054599883356218175227331452924722558549936960733419533892684504472716145406068552393021232726327979635228876199079965686627072767760143813112977632709390627732330807247612718081853317533368977597841535037065250244845293595869833157234580037901524982220379728456454033998120376310912300218496266262777387344074565011593368670327711483761631037639070577436688718671720575540186699288312545280 := by
  rw [PackedColumns.col]
  simp only [show 9 < 11 by decide, ↓reduceIte]
  simp only [col_11_9]
  decide

lemma col_12_10 : PackedColumns.col 12 10 = 1044388881413152506691752710716624382579964249047383780384233483283953907971557456848826811934997558340890106714439262837987573438185793607263236087851365277945956976543709998340361590134383718314428070011855946226376318839397712745672334684344586617496807908705803704071284048740118609114467977783598029006681129370886417827884046127656956366228892478256460574066365210290771821284975289641976879497160717152633965328563257396990506204493271825517833589428002008947976305421968653169489800700043920461069306004176574557017203334673772721009211507464275228928957284067323355657482772548674267805293784364913069105690745579399763137016726168676614418373815785804419263443829994913528343726197924232233843448230234354442216902501675118478607266340496883906056813968109678650873269623047506144251207192348736722002959785894766663346330782590857255426849356308544146420467254325915846046997571423088052709552219416707951538967168791556618640795272589062502312550940406613158238821101345989328956470661586832993202111821078441535291621023613008604897804903434271160062834068634843945666266783530255900254990723856788556496635177956672584474648141783972986500343820889912556558586040315196548818440919773527784966907775417291159271196590080 := by
  rw [PackedColumns.col]
  simp only [show 10 < 11 by decide, ↓reduceIte]
  simp only [col_11_10]
  decide

lemma col_12_11 : PackedColumns.col 12 11 = 1044388881413152506691752710716624382579964249047383780384233483283953907971557456848826811934997558340890106714439262837987573438185793607263236087851365277945956976543709998340361590134383718314428070011855946226376318839397712745672334684344586617496807908705803704071284048740118609114467977783598029006686938976881787785946905630190260940599579453432823469303026696443059025015972399867714215541693835559885291486318237914434496734087811872639496475100189041349008417061675093668333850551032972088269550769983616369411933015213796825837188091833656751221318492846368125550225998300412344784862595674492194617023774188907174299818431120503398938670142390167527982718281038672250482020056617189028439217958762461661095296946237237440488670954249120630699182954444685807463642006912490558758032756573144864958427211423010838419416209904320775931621040854102139836942364029067786745528754801263275255572023493503792206541186428523051062105479286926994901193978367674231926737841718190431468443009066164503568191274591482133452385466754657575807952456415920200667342675683651625588293191772291620716891753772421453754942251261942325159403931650834773087264785777247077752391129614356077901998275463259428483942050248854729343557959680 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_11]
  decide

lemma col_13_0 : PackedColumns.col 13 0 = 727165423746277286308656163155855241632176107997488461621221857459814221232746196810842823016801324815971527864104683515406580546784789375740653176718369866052604199228128659692406550152032136773131234409061092131181257695072883040080860369267924200678600168357199944800006719733351023891200603531870587301567001086796983769274003541576373343231617356862367497229285945835179130852896058703745010462899963604451883427209933744070613504292336385342217662377224031494938254961874830087678505012776599484243829148288184912050018418588696804334528507800630466112331505253122567824699997933974080343770033410374180994328343561403832644419698021857547670487218953481109980216264092423501084273010778670285082290664205947794297454124937596873776936590492956555251618778271663580662341245837573313593411347882411166305747313238004175741388471143605438044383424854018014873951709940184506107013918869754940699576379169947311548654972789842284922526848298958679017985176627381810407720289793884972893327974276161827607066078284040370989175837543018407575105752255579080771995758680585691783696891193277129489622637110876713391475690313503780208002753816997223005571626435885957384720652367052608645271568520036623747707393863896781969410648618319918351825706672136079039286669851832485174569209006995893721241065768141070640205570937294547459809358579150812987665818402435744199237449881608688990292523549349834279611455341520718806486202358248536382914730152469081850909296860579870838948236765671714026412924966419911205459179775210518768719595452728762432227174492387879708668662948527169970040859212205620053099128821452772510612023710144104743601994746850770405248738624984977894352241991805799633434687487908396135390462559296438040897491136156017880735305969967464724717697457748530863024301080504339567345937349182547693021850805784652393154644220205928869776779624123385567094378891296353367624994207532556244843492396936602848970619149299683484789744936245236503073649584679845350384403920692051513805145294814651393590292390562730328077399901692602649770469295982057393953731308907178353309958943065457137309169707664903885209082555525937539336192011547616539109308447555685339488505567248706409412482520948067640132410498257903397930726126120294226372349881911694075475092529117045100226908646687953348931885643545698158829488018676793126440279215317333876958407101502846775730433916955900764748809484844403602387854312727204384312633725107998124337110317143861930 := by
  rw [PackedColumns.col]
  simp only [show 0 < 12 by decide, ↓reduceIte]
  simp only [col_12_0]
  decide

lemma col_13_1 : PackedColumns.col 13 1 = 872598508495532743570387395787026289958611329596986153945466228951777065479295436173011387620161589779165833436925620218487896656141747250888783812062043839263125039073754391630887860182438564127757481290873310557417509234087459648097032443121509040814320202028639933760008063680021228669440724238244704761880401304156380523128804249891648011877940828234840996675143135002214957023475270444494012555479956325342260112651920492884736205150803662410661194852668837793925905954249796105214206015331919381092594977945821894460022102306436165201434209360756559334797806303747081389639997520768896412524040092449017193194012273684599173303637626229057204584662744177331976259516910908201301127612934404342098748797047137353156944949925116248532323908591547866301942533925996296794809495005087976312093617458893399566896775885605010889666165372326525653260109824821617848742051928221407328416702643705928839491655003936773858385967347810741907032217958750414821582211952858172489264347752661967471993569131394193128479293940848445187011005051622089090126902706694896926394910416702830140436269431932555387547164533052056069770828376204536249603304580396667606685951723063148861664782840463130374325882224043948497248872636676138363292778341983902022190848006563294847144003822198982209483050808395072465489278921769284768246685124753456951771230294980975585198982082922893039084939857930426788351028259219801135533746409824862567783442829898243659497676182962898221091156232695845006737884118806056831695509959703893446551015730252622522463514543274514918672609390865455650402395538232603964049031054646744063718954585743327012734428452172925692322393696220924486298486349981973473222690390166959560121624985490075362468555071155725649076989363387221456882367163960957669661236949298237035629161296605207480815124819019057231626220966941582871785573064247114643732135548948062680513254669555624041149993049039067493812190876323923418764742979159620181747693923494283803688379501615814420461284704830461816566174353777581672308350868675276393692879882031123179724563155178468872744477570688614023971950731678548564771003649197884662250899066631125047203430413857139846931170137066822407386206680698447691294979025137681168158892597909484077516871351344353071646819858294032890570111034940454120272290376025544018718262772254837790595385622412151751728335058380800652350088521803416130876520700347080917698571381813284322865425175272645261175160470129597749204532380572634316 := by
  rw [PackedColumns.col]
  simp only [show 1 < 12 by decide, ↓reduceIte]
  simp only [col_12_1]
  decide

lemma col_13_2 : PackedColumns.col 13 2 = 1026586480582979698318102818572972105833660387761160181112313210531502429975641689615307514847248929151959804043441906139397525477813820295163275073014169222662500045969122813683397482567574781326773507401027424185197069687161717233055332286025304753899200237680752863247068310211789680787577322633229064425741648593125153556622122646931350602209342150864518819617815452943782302380559141699404720653505830970990894250178729991629101417824474896953719052767845691522265771710882113064957889429802258095403052915230378699364731885066395488472275540424419481570350360357349507517223526495022231073557694226410608462581190910217175498004279560269479064217250287267449383834725777539060354267779922828637763233878878985121361111705794254410038028127754762195649344157559995643288011170594221148602463079363403999490466795159535306929019018085090030180306011558613668057343590503789890974607885463183445693519594122278557480454079232718519890626138775000488025390837591597849987369820885484667614110081331051991915857992871586406102365888296025987164855179654935172854582247549062153106395611096391241632408428862414183611495092207299454411298005388701961890218766733015469249017391577015447499206920263581115879116320749030751015638562755275178849636291772427405702522357437881155540568295068700085253516798731493276197937276617357008178554388582330559511998802450497521222452870421094619751001209716729177806510289893911603020921697446939110187644324921132821436577830861995111772632804845654184507877070540828109937118842035591320614662958286205311669026599283371124294591053574391298781234154181937345957316417159698031779687562884909324343908698466142264101527630999978792321438459282549364188378382335870676897021829495477324293031752192220260537508667251718773729013219940350867100740189760712008800958970375316537919560259961107744555041850663820134874978982998762426682956770199477204754294109469457726463308459854498733433840874093128964919703169321757980945515740590136252259366217299800543313607263945620684320362765727853266345521035155330733152617133123739375144405267730221898851731706743151233605612945469644570190883410666624852996709918133949576290507258984784496949866125506704056107405857676632566080186932468128804797078672178052180084290376303875332812435424746988769553261518089441816492609720908535103283053394849896649119680394186330353708647162966827548389266494941584801079645378096250922732782853147379582660206071141328938528475920447732510960 := by
  rw [PackedColumns.col]
  simp only [show 2 < 12 by decide, ↓reduceIte]
  simp only [col_12_2]
  decide

lemma col_13_3 : PackedColumns.col 13 3 = 1086503979449690575651844228217308999170255352027375755885405421262913077639589648153165930110707037857327107781385986264265085330604510195659186069493595441884046741259149437050132744196032453388647447521709958670714408384855980884790079306610439272609270290463676182113628717422594525969731641074857219936971705904007944620238199844223063672377202587685405132046870829574742358939735745300537291897873875580192697416531574154564652084234463704168916662851572093751191789515019201376142202042436631135990779739076509751856836858902955536437583451344132680883794933919062513792547856835198625883298415679313951368957525010035298581545385371180149048510085907146872499622744791792312904127767077857546582099669475034836615651299517654472880714594355234697340940120063497334530502094947969464668754698781501509188353962192193009668066820697060265404837490832462714831118508237474125856394337922124113730106340860932947994877469071204036615759960104280672151386411770095778974959499147283383622715728101346855257250482727904678832075959597350461123893419712616214071775763942976286556185238203184504762704640663722404444850836888659344746587772240182621144511690861401586131255760735207010582818219111650052603578362816094802631337311554221200961482767945915386580101483358380055669395238360647561046523615778078486870968635174790296593645111651338179716979277301693874601195255854232438024405949583464343826345520821571813313971601967188474595483487854272869380346964958998717518117209797735168039465226408969828415939007913155016370382586201742586669164338541155431160034111176009467970800349951311121013190916215711535580058432313989635103280801489457960449865819579744091484168330446900494393925758736796980996069796197547985243986912826007435277051974678861892818255236668386909927631640524955900365217276039245518731985956067787184898721336111124812007759857492853618901806387137189882074583648932655648241322572297368309315193454293117036802176116947541520689417437511739535465165801967104076970043485576688039436337246217805791618605920475680775943625915212673579919370555730040297617396981455786519613722650458145226038600341250280000058774699347993325879447371376892541518924459680247094401612425245307618575139477164712198073172758102841217832400709551183231614717647981248814468821528872872272708131689054947657949379468479268048873747343263353526104093495435708533703815123051015820597912618062958175032361618895281114722085802920005724823912258217055420160 := by
  rw [PackedColumns.col]
  simp only [show 3 < 12 by decide, ↓reduceIte]
  simp only [col_12_3]
  decide

lemma col_13_4 : PackedColumns.col 13 4 = 1090731492377649913076371140926090508772288022347454197342151662049370236722216185228086315727659756087542381786669313644178532646766436284737006116912929052480815466086667985449476379848717017461066159075763944044793663983039270860309579287128095894281232142914478590317223256735391291218709799496421963380887780564207862618897899570488789617056638427895664654281211004766489910727727759201869928567754368100035673717570919126251088544271996521425780323822125382487425579684333175106262840178463933895343170737038950968066359623128053628535048757661064396306004795648304940834022134014394738759997701517820826227420441665932867910905808846005834356158743488457009559411929525941069176013153662608964473953666693646214666782585377199491581365863433169067968554135514558442306342887694230846994624550135534847376599232197823557564146242081587332064559992017476950946319619359444248109371748486692855799489698611814707943283617576829210629477688865539069261394552743917809639143313973756326583543848257378462564429616241730696091062171503561065325895232765192882741203763695870971284992282098111218660418751522767664574753593551408755505554155839084715661988085587581566973581015461353733620165345862546046674315694133031863752093388494672036462729057916866275750767303860636596466131368879010701380485553645594699302909325196756079672385052501103827150151831976334641466070132492510498840375913377104324412513915893203117957074929225098251683568818116610778983960015236926371712955543693067918514007296273844438273669212942647585898655890739354078797284894964671836167065386613546773833634383996775276160029552156249040219772103984039642838626279683147201335391793975777396995993145807139132507822505131625600404251400452096938297028960261358945050090842090295278274847010557189245433247492155849346122470894688100480162577170477926277810346432479715635924966607323646570559953092490196327592825540237991980241590165503279915261077067074366481305045563364399525904422723786141683588265993912136830065659108641858179205570900455649154556530215297251775499077409916111817294890330692445660632067110242139656963639480277435505310459643431014873489279414979373131151267245336657370517617194123667803452567018352064922735181294255470115135422465189162296162920296668926670039756221615001022346654653517921366037709997197050769974298091004898049521668450005074312059455258124511891747278706315095791213785601531930729995714415221299954221210448230969019753953267507156418560 := by
  rw [PackedColumns.col]
  simp only [show 4 < 12 by decide, ↓reduceIte]
  simp only [col_12_4]
  decide

lemma col_13_5 : PackedColumns.col 13 5 = 1090748135365456339041586926824709096400964067164273332347272707540109023476350483456643682700482416018057609895981362120404606980048375087448667425214590816869671144547395038055582970986878455636444962424714107236239490619974692554770930709212877821728916669614260327992795699918566977659395175021578144334544566109855586642133164142480791907459073081590624358274300179425040837504737754591061664838562273108983506886107634298866042884653729319819199997516446804694739144110610717674156946529148702714412442293984696868969709907445224692898230111221050144866923794893547112852427041007695329043678419482870554145720540889865230465166845682064128327460786411382323751884924288490359559578197608978570342104424944587739380487102228316436132266546300897104300298367464939913764498334082754312722554117819014494666733843304428703937824198941703283915032685136815704633686814941668193778404358975865825028806933982931557049500470592340750507523610764520132237088741246609468819349337613959440828784317324935031505062497594936585663442849809668662650964255879591527000676094851237579633838846544771148541303921518249715058663926914944350215064247014897203907073996515109866185678977480329325325801747949437443546148220516763024497923624659148936397529559134468581007943125037851605844897637030937792984208879998260560834990466014491803030020045397864796326702999835042686266982263606726267146269373602788359121917286258255297088099245591502185867918926029084430605200919372173516522535733737890028181875115540306551779084866614357067231533631720626002919587235295062368071686593937750462360071885117835669805146321374038164582655652795571977548739307436252124465110216812285016292939828102403759493188093620266844902118992158588255074301105296020131705096904108125908453231286645621791511653515435611337191921902927077389109450451989403004404527133421488734171726166453908082112971477795474787089400560567367842496129965928562701168456383421601224547224975507428722506692020725843928961435818309035149891715365798426895257374225068707636935783558936310339766210019945402769632483047091147946123851035813219440350036499475353738431721176746185131364175201392263406813394131677632259165477572009757420066823456072165146952257899881163435108097311824032068432359543340248227743649736365547338111070004318372011931585654645314294836757658558013694582114506887325604913720922722968365137005114262182509113579006044876988892546771973980841489093151046977170736321405274931855360 := by
  rw [PackedColumns.col]
  simp only [show 5 < 12 by decide, ↓reduceIte]
  simp only [col_12_5]
  decide

lemma col_13_6 : PackedColumns.col 13 6 = 1090748135619415929403854669820128643835281822143174671095392721590677921920417072578689030872885679376536174029528239896742254073353278082923030058229357091300030393146888777261730166167240147960083923101996823490514355455651568890737193309875090994887952495597058554419219395583801974058669822774425700320602000555580027419219660782965643544761919466940595449891933698401109894205870007440326040697196084961016514337994471542752611988248099510093894277317118938299181052534179992180611763502713740568706813166286568129787497207891105101070642977075903571570054027644364590446601280785149886722456526311428692503745869033851011170379573239871025633307907777362710306567563441148121858767949811499260469124776695938902641931594003381934561985005343743685083799012958615340497526215585095341939983925335426324943931358772634914039415810241181336029872642177025788124259913276625707191883433362498148979089190612769477364849156296598604956531440099537350932558545961732221916191503815951153776287037593938459242959091504280127175810734425619861520616741230751469122342495262459811324635237600645624320878844480106463393239977750409859338365102275402708239345773880027238141707183621557733481314949378274404868584905321709416744565607290993339377141986944120719563564133545054356921532678282631495561640293652704448981407979637281048067370092943735415862513219631905132205243835345916182893926006276981822640099165954635101713781042208879607159383576070856276803186793994557281304652875534793746532044826511343908913238927973380729497620328575369613527557267407888667221403469768087071709689761333129469855333306317190610121128804688744301302209854694241778786633133327396692416385648538584937903813623713078893779055091594531543783419179722909182516033055000345688034320365228169710990474860995658072338681123651241223172931351929918827568679587283744611196323840052692029991663662335786495300388236002058368899453352397682826240056654577137531924806502740465564271415492629087478374350216697724571799736835532009208639156739698175298800515035510452484116660223014932861307476880632787267150057929595142785268236485943223275300709970934124908318484485834183562070916059435823162768771276983699787719886834170973112315811783258262042268793707899620037982010519892205757909218844019984162560417654567467164875084760799557738260877398316200197677337735993893876640054030862480179650557345729971470059927578032767319931222828570259113571184368826210270342110464355294248960 := by
  rw [PackedColumns.col]
  simp only [show 6 < 12 by decide, ↓reduceIte]
  simp only [col_12_6]
  decide

lemma col_13_7 : PackedColumns.col 13 7 = 1090748135619415929462984244733782862445058741317256278077723357411872937927833784244419600432340383621359132078539296421583922726078535288895631126147893430149380770045156693316471592314481596094990093519266467060963746463149021913517350803079950400440665964304739215704920738623747423257015752366908264085893021118110308974552597077954159980749712419298225792610335570650809591039390908475045801933904902676564396390725443722970902476505668943463129909442136980589661502329916207474552401367763852856835262959009067319505910523234201508849530123021140590765937850147753368424740552323470408182285922748805210520738945273624250073532547213864411288330003393740150912580166278929704842831018825970092592589997564992748701241134099098189591461277259179911627931227354401824729735222739283906940258565844609867958833251463899830750255317198113101160530620734317932567900498223532817667589142046943165554232191512001478956898687683520250475974324734315380150309747612208712500051022967476984319077129296386777374636865231087169447708549517544139233017684215770290488418789440168334816327372623519038609022141979462139722689427219151234633118646875003741836690327166568052540560892638150017862105394046379266526690121410209850772135746339395758587591648792223654974745634225736271050568271311740257450712934213663479668020824855253157533409992242243185229562856090869187134982573538569852483225539869705077626849803583477586364785204481055628574836838979480433938208897652545831398860133527896735028968302348255129557764568722621963320682441686446392311846397899383114863434253848663932279264188564128386706056453584844520974679854641137384660894775927042925383218566634937141648684602149056050732108371054310349389279475071554719181040574555552962971974792722792653974763290140871652286270098969576677480222940290795746088405409748159994478121367758864292622252744789474675449474741606852764070764063110576030660846709793102667506631035454077016208694602827335899556351637399344567778304083178028820294133459605355876156179714463545661793044235280409193608501261558804583167350441282704397497970403108257267112393653696672675910688099839367469282734578305725116229359673050529813789252273363198230132949795533051518858815503461348243733779388689730783814640911372667854894579549420746122021822981211980082448791461461735149685581518666731366228054655612843460369296145991464644624232666058546546775071466057342070960016482455402459983974533531512623447503628532879196160 := by
  rw [PackedColumns.col]
  simp only [show 7 < 12 by decide, ↓reduceIte]
  simp only [col_12_7]
  decide

lemma col_13_8 : PackedColumns.col 13 8 = 1090748135619415929462984244733782862448264161996232692431832786189721331849109875331513870234605433463932241694048131051358947830205980188196448074959461356758486573232462591433156779577237490627406123547618423722668866652339479999293626021839890161927470072222416275310966999593803517697609822714708579884205550840414698745794222115405131762724689518277473450666725768294443700706103254859716733899036477127355717020008787842924414391583891235738543020558099725138939596081148014590965124539186821561529914566658849262988504621375111628343614858679068075902419555944729073976404444565343555827377610000620947577410278627011740831480055497987845581365988527549373552036103980380460119398337457819050480022405702325635582620236066168807184261870584892432597683277669260204163001806232850994074559052885958077900805983585439963419680319621217850405971289333030803245070840561728370555174569443676693629170452149296065798196661572238035681751946495873207469100150493032277188951439284275065790528306049503847529562489086229780168252138484384622224460015690956455991882709903488025930330456108229822033526376707136090265975193250434767826227728688689631822571110448349847083887734391639427413322727296020796085661840741564416933944834885347677704020625164362236290082483231096646670146316488035415210816619742524561606952935611302947966659440338951555748352481673455328318110092907812432976349828140055049776760942184789064042974347999533186945347522493599199813729152746600124370793863684351800627532861582603373243844541669894180917405990955855670211102417040532303109059148651080538307108200472206951864724440163912445823502524921620535906589683568560322180265439851314707032130422408981737587067461745778054108010454979688805716669890106223718629918609636282362876953861912714996254991032203811132391157099002202347885731138448079694323323449229027719621743895573011766662593894349081522104383894908548239240269319053774558041228754281281816861897527545504098214377454609550129806936928314745701910920161391616609369496032529549582045082542643910019366151847658440920119593061651167368561688293227455295170854030179178723762426736301386023622466277453636011514339531108046811378554467570571147700293987047007133169604516470460363030434395212791168390261169656611459540138630944243057585634982081359365277395087425491626723439059966600654655183801562224994052115182662706659658702893140791266483454391692605083442515414863001025232435847470731267136086799620306370560 := by
  rw [PackedColumns.col]
  simp only [show 8 < 12 by decide, ↓reduceIte]
  simp only [col_12_8]
  decide

lemma col_13_9 : PackedColumns.col 13 9 = 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554717727193825132424258268072070423477350441019325238935081369672808088954075376607323183064685826513719267367765025669297838401423262150842341357600244555889201894556085847866483922724148646867108659100934137092282466892797007055681424336981376513709740535026193493673249209257320971410979203369564857482654510028075971351626483674957465557609650341383284243352703413714646767970869719760282612297099758526022496503350912508240831354915423886988443810272342344732317150627439462977141579914873924393499344568782246440509166066283446893682365040319921619212785451204784909812620149202475072920645750021639932387054565814599265491865025466591172979897528545547657398713095194110513475640015533832552892834462456004562452971528736770337713855531343214788202807563614479213467081621550379582167079624431075961285990652132534019881887236124261807921871717536754538527881569172145267614894322853623609813920928459120198997814593256579843388566344082288016681611654470716138650900737275301237931416801181903989453821932064570156865659395968836640923032250896569702084633936822519618352768176774084397451792927718879958100081887861393908320621408161687515022883010853676704976685223953947630891854814753738450680771222651381548932686869654811143303224385700414066978115266169823947267240120243654344301634559922544942816043553794364709175132165894258852632905428043741747989065584385717223677332433400389608789558933209058517367950612903452919800029473576992005403338790727107551494317528931418468321870206715879080915763252955490226179218331260318126443739420462473525613282748278965996483750636045783491802222016697761633212650864259383149056931239290285624805626122759894380826805436467577805724137767574570906567601847329444596436887515074101490955904440736746378578909097694701009073306364306371857928229086986807866811037349498795349771504573858928341772320617473445645992985275412333509090804871751065163475735116124159825908647121640421907667647356208564338125924147715960797202874727558317522397417637853954101630500329587808124225607721416501990667502342789749660037118355919877562034711995165307625661050344070739613757088494470672876611099532221420366583803436275263239830405586791170387133117796852392016463145034898659808641129024904249424733643211466577601264042611135606503976088487910839773519358050959360 := by
  rw [PackedColumns.col]
  simp only [show 9 < 12 by decide, ↓reduceIte]
  simp only [col_12_9]
  decide

lemma col_13_10 : PackedColumns.col 13 10 = 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554799078906298842192989538609825228048205159696851613591638196771886542609324560121290553901886301017900252535799917200010079600026535836800905297805880952344434142288520078948840015587307354938660586662128298270350249817014271693665765110592008613298778505422237692146259873858659415573867216038413367887863225808775353059030740090896360912642226573857037049962736349533220384817969976483149973107413139227644176078619320341055567499174066505299371568329139777241183089138566334553194650577629094056611619967969653726624148744303488035402293152604489486492100208017863024726771025350917773611238726097375366394777344426511988513556879991178832915713510549481697173215445101845957529458649240419039109240935740910191672068265273719092589036748465496772589128171977093240953165534992672018013618814995161462309538660641385783569275376409313809965475889555022982121273477969648053452876833585167683334003690463172464081216829623878909681066796095037273252169666759578152053991219528513242729480885311699333643283995611022633415058770494955457423321606395672379513094283755488117583208734138564299317466532948220527445976808475956204587074983904100207162912865380688486391072610835612762060729181212793646168221753156439697858063620473480211440842709029593612453629476963272918555621144668718781463666529288238422362202825387580631554852164914519052059660040464663126781487560119934326441860936571324105415002310162950779332518014848112844743427605942506544050522057943770995582957029023526909557365112077631459260712531564908022807631888258826691914906113986248716550085419858013381711311649991056871703624067763554136461504317273126870747233315465647396625310067987550217403326963292546153158772672740041967708838522805761174003091611777775043411335156923698959839678510230832295163313316789267444620224432518792403169045198033711681799380593647401842461843648423716417664365528718045683794601856283379413891052412969460121927658025990683597601528175797008376299141662638078090891860989403913605461823884961828737140171022361679405979038786444181270716007518309822554612689912150227475032388745809549109277022071797772295031123798251651255599727407916691739326020171853970956314931166813991316312725113081108713697206841284865031993483234062808071776305097470274820616405375977422257119466656882704639478857686056960 := by
  rw [PackedColumns.col]
  simp only [show 10 < 12 by decide, ↓reduceIte]
  simp only [col_12_10]
  decide

lemma col_13_11 : PackedColumns.col 13 11 = 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554799078906298842192989538609825228048205159696851613591638196771886542609324560121290553901886301017900252535799917200010079600026535836800905297805880952350501630195475653911005312364560014847426035293551245843928918752768696279344088055617515694349945406677825140814900616105920256438504578013326493565836047242407382442812245131517757519164899226365743722432277368075027627883045206501792761700945699168497257879683851737049996900961120515655050115561271491492481590583927528068362121611832823090350947768974356780606151520143159909137700592185973126172549006476832634892320043175548198813118732027663641737580234180498216659031323755528672469578345747574178638520542422428423677558820978627530386229456967934723788568179648262880758976714398711940255399001607683329891312982140614519561421728861174053416163557141099001227260702498594974247602767107850237371185829184296776123032637607387534110972932388406207584762847633426555552446542114214004891266591088458003495784055858294944168684601688858744297754455478086944868426545830699462053020840665064540392958400443325645527374926882973919246656771539390355706463348469275233864897316857752844929570354333768590343841311070850781091725431885844774325016901949773780261558722409401181833978850211680880235006737620395003207721429913359698783128999341087064869360477360260946612352621282830392338045342868360685801099549739965616135919539306625022788065057280252729962269737132309764754628744321772059641657719823547449320592935611616099240742902136329711517410404030324521840342033994485065200736874265167184988389293259882587602113424959054628993094268364393026247954669688793470940786540624498332650203138482502473546445070830271563685172304095213304349600298515635788989580172037008658825732196098316200861698353829406714272630544531590748563008319858775677970324879375646607814716537093794936528532510075217655406621358266156154358999433998158724863016801311862884415003624026624271858216959376261551815071325789099581359312420237157949795754513740566131017746235944565634476856040075065074597078314422621893894702231993235077806982696786165968173125570545073461288474360408005636640266535246648614607443110206856314723120840607763815821602035459921424929857198102394553285216706183381968298312489240849692137274288006245419386744015437915115941622091612160 := by
  rw [PackedColumns.col]
  simp only [show 11 < 12 by decide, ↓reduceIte]
  simp only [col_12_11]
  decide

lemma col_13_12 : PackedColumns.col 13 12 = 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554799078906298842192989538609825228048205159696851613591638196771886542609324560121290553901886301017900252535799917200010079600026535836800905297805880952350501630195475653911005312364560014847426035293551245843928918752768696279344088055617515694349945406677825140814900616105920256438504578013326493565836047242407382442812245131517757519164899226365743722432277368075027627883045206501792761700945699168497257879683851737049996900961120515655050115561271491492515342105748966629547032786321505730828430221664970324396138635251626409516168005427623435996308921691446181187406395310665404885739434832877428167407495370993511868756359970390117021823616749458620969857006263612082706715408157066575137281027022310927564910276759160520878304632411049364568754920967322982459184763427383790272448438018526977764941072715611580434690827459339991961414242741410599117426060556483763756314527611362658628383368621157993638020878537675545336789915694234433955666315070087213535470255670312004130725495834508357439653828936077080978550578912967907352780054935621561090795845172954115972926435488646325407501512365848213380395168763512806429730109607098577644744240048503459529594006823631373147762011780218660740030215430505248911586325182120160839367048207709418842650690943826010989109302792718425868852384783378651199618535121913835737651699662333815683378345818068070160548347800369481364172406204671458973952634913932812733482191175501628465349005403383205634207163186366050321349674463279843106828789837369958673440743379029655723491233599261110682223445532527992025505094106028374148434683256837486589543018181873279720349434704460879700399438016504650780473547823239120431423814382915239771713285086798751923825359346515261480728322427217167293613096521198247560588729708788376007087530154941809492620352947595475014394229254625965054086766970439573627357949092810593883736061141168581582787315634913260797956280083967967201275577888581524322407185240031043931510925713450658807511908275263101371880394716465807521940885628037330976885109586390268456528362201664202524947917653322271271470730573883899274644538470640093205628124760082118516398285556726512915645798229781241791101398278815512033744564071010914628794915292515492524789530849844709747037539932187090270337487885794730917151571753381797325072561602560 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_12]
  decide

lemma pointWords_spec (p : Fin 13) : pointWords.getD p.val 0 = PackedColumns.col 13 p.val := by
  fin_cases p
  · exact col_13_0.symm
  · exact col_13_1.symm
  · exact col_13_2.symm
  · exact col_13_3.symm
  · exact col_13_4.symm
  · exact col_13_5.symm
  · exact col_13_6.symm
  · exact col_13_7.symm
  · exact col_13_8.symm
  · exact col_13_9.symm
  · exact col_13_10.symm
  · exact col_13_11.symm
  · exact col_13_12.symm

end Q3PackedColumnCache


namespace PackedLineArithmetic

open PackedLineColumns

lemma complement_bit {k a b : Nat} (h : a + b + 1 = 2 ^ k) (r : Nat) :
    a.testBit r = (decide (r < k) && !b.testBit r) := by
  have ha : a = 2 ^ k - (b + 1) := by omega
  rw [ha]
  exact Nat.testBit_two_pow_sub_succ (by omega) r

lemma line_bits {n m : Nat} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (cols : Fin n → Nat) (r : Fin (2 ^ n)) (l : Fin m) (a : Nat)
    (hcomp : a + joinWords (List.ofFn (fun p => if I p l then cols p else 0)) + 1 =
      2 ^ (2 ^ n))
    (hc : ∀ p : Fin n, (cols p).testBit r.val = r.val.testBit p.val) :
    a.testBit r.val = decide (∀ p : Fin n, I p l → r.val.testBit p.val = false) := by
  rw [complement_bit hcomp]
  have hnot (b : Bool) : (!b) = true ↔ b = false := by cases b <;> decide
  apply Bool.eq_iff_iff.mpr
  simp only [r.isLt, decide_true, Bool.true_and, joinWords_bit, hnot,
    decide_eq_true_eq, List.any_eq_false, List.forall_mem_ofFn_iff]
  constructor
  · intro h p hp
    simpa [hp, hc] using h p
  · intro h p
    by_cases hp : I p l
    · simp [hp, hc, h p hp]
    · simp [hp]

end PackedLineArithmetic


namespace Q3PackedCertificate

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open ReducedCheck CircuitCheckWrapper

abbrev I (p l : Fin 13) : Prop := (([1170,113,2584,4372,15,4674,2338,7169,1352,1572,897,2244,4264] : List Nat).getD p.val 0).testBit l.val = true

abbrev pointWords := Q3PackedColumnCache.pointWords
def lineWords : List Nat := [54414283216418386405143011182585610558282940790406037537492004062163054016644572111417355868763346349676566992735216627690924733321631236620916549449564699661430743289706310014261474781234089424342126221073254538459610574591768736076319966194600200640867076304632086538399052734367082184744716055813715618595613890029235408487241047198643551840415987197723111238479647178147834653107374257007824323724476504536236747946638941916115120386519747022846997537219188655442842055263771010367621012251156923647784604660767225259562785129794558400774015341389746680715763478428862554837132284210612274671700884893008257174490452564010558207871295416509414841554342170036538655798928085197670761089418596768080944419839007813329364963792816334763758125835312423935239770741193667568470190281161323672241312308811377234909781768777848976252646365422984565783635199625855680940302509899502663099194365587412026093148028004099700864933937515315585722270652162565013404465797387368440550375757981806905418414112959310913325391462346342091196238117094852015874117335272315579671417695066411388228209347486887153870365679803116331456106423347886929558325116948247079545856468475067490881683284131425018266001923794034816768311330436053168593588079126415200543704281122632751101274779722317948161276703987778534481237371363151675271036306649456245744911820413393584592093135296371036036740575874839973483246595575343330216225643305289931662403382610293860415139890233243790921155720504828258754035463962077390180829002872300689045928010722209861504440102880642878632929883057584031509149088219304457379557920039391581005475557558311626721377422343047213765245929000517587975522439806001641536850760006527614273042119165370663997930969426829519103691413628273025165159429800162969444610456479290301823439814079505518475993543631694076876552526159764434117159002185138412065509099830881358122227214949342615991221410004375738963495379745443223499495490544584543144984089720533741521755712785081533799459772074479022625245198272753964189229920820551706239225274358698422189657663868235352323608761572854753219373437808280066993435443, 70022414732239771565520471652098165210893541944689447614725164474251237992496875309882161547426879800517680558677962207757258941219970722619442277304183978252343294390393039387207234322095493833074196126248378527145912088282141160246154455032654931485724380926148032438865286878812046758764972047424429259882894504388680677857327479548285155518456483873577702823010416911256790700292408936396364713340043975842043920321139019259553493464791831906386322579197991441259615455471257954598866642564049834475640514499984422151774284060205384897335366008194542415936387818962870938845399560262109161101127140100001712562513200840195843864338592310757828156652687451414634626116524527966523210276593638912284551603371208123512644513431817954193037134415721708576726301818580031081282654857161335080338875719831293796505948382744423437238579927512093222061262196130166262250955583001776264517130573785377465816956929801143278405115314449147310206693368177842313829927299424485992243799275059502729771626234145082577392992688921349402151359742163529957447417841792994908885733677859868852533304410783420003915309337258257882031407523826954470552504873123041978857551296752166661181346796836720653905837903756168789510442144368481509689854706459003438556791878417361835552001064410150782873089096597059375029222590743302133530233143553017432183889944821288622299809668733606342094889478865114402524016213839824370244762813418058100191189995050829158554169974763649188538087527710986142094540253477226723144445725979381539574674872231264923877161277390158816470395659327739330282409705854733787160116678648643931478973209549706504448578273432279122053359888505825300727967055266099331437916958000273846655189324741492965733491366668774479584208940973557858439615236193659209141109541790608843790263139898333178670444935095084044993674652012978471737263772403627363778538522117328809430971409679631388768692920800477986672293195038393569095672501608088369143997235321324448732307779925176247412447790486933423627584468520773411709999339868325816429771661877914121900970406733087187928047033889863425843587386135930533834588396331755828085945455564870867892426325317751695599367594810486362170672389912572532887873614693277633172865041904776220775163733505223879420945095729634202306758132168362831864204931407011017667717904847932550185586321757159409739570381614945732740134863897539246886713637862185554044342010841562839144004107161787454805, 149456875514836934519504679603006855376571507731929646456592648340128321926408918190791542838695449039486855607878950332353000851246928509443993630108626591537143064195981135092244999853248328911398574396157611442432122676880823710266845825934774112256218950150616595246156840084680971350714255054996382634976614487931436635195670471767420868508577226585925243767833414120403462828110360869296083481723194267896426618198467556701579249141685638259954890885026537594986845297218211668677818393941754868613243801937711734470994886408233874852791633668907351637363684223899964280719450762998559758301062459026669605678238436208651511812349558253847814306178330085031231822086800592271504302827473067742883853353551337691519977578443960609059093038951960474821689033447842285368678280620628322121941861826025471393922102128688290435231781498251382727681358619397732907577385391858080343648031099774110516989028391872125454009070244541738146412895273346568294727523167930895000074255162716864804702400192504502497349605821082878527139682821015546616608688233601595534083627276949109529012403918543530273475440943418300711979287735122737524445053368511501101607977326267552661311544401960007728222900149065453479771482526881682345185434857493447393610570625198523498009888792093912951454737900260460470917714272764023496402851592859261046951723317673129331506643467141102282292690069530653812392169421769018428305218725595368942362819736501234572979808260511758072979190720817234968310139408888636320699994217796143219115866479428869488881231463768754947418593368323573864364249738793747249025310706502488627422471675608957827729041418363173649174883495010759286719889390585119840437309737533695, 8095578175373344162456482226484754152303256483338572464675199126990056146061083361865354496557646072505541214448015213060289639599021018447790612358208188289149187539236392942803310595903009879236501442706250389958074956148059270910157538465913906202104552973972214118358990409814852824204018201697270379595383156627404997953739788368163068394904229240412009810602260320458035623817362789926537612728321026980957415284050822091403686260061617895702762797455418800660522582452661243315789921235242504757698341141060070715355690157164745309685882246615042813596747837452321685190015454200184557047173631497632199654207350453731200293652160209690463065295294887234513220045944476525183898996236245962606802805864786166330901966655990081726764131772158323987467509410757958607647304483555642885106616182276730303386024962734082403584188120642466037073987181952974779101160309981355069323683286371056707684351741314164909852186817227346063924470132243367107789748122428624392858587901996680752542872371008126189286142424352975668141824996061336455580212481426105692623643687391948639016153035541609720784958935045825268770269219324033310583440096142298895, 16643749685197465926039280456760248149054156740615437436970058536502957684429988482738448684293919084824251038317800034685433292441858305693308610133173949783762970913896284268537572674571575572742761144634037357088149638248406569926318616829204032975019459106367588574044557558556901439487310678230043197563904808578553073226688110358809186157739010228023975674737604619711126821993501000314603123435567947000500879542456711926541851780552446448666002801035111730257227167815857864217864614620659177941035228846147514581140270510155568879252197477698110920401270433809168409812313983382331891594644848028706362882315027727256412094751614141852773414676561077617532163338615070347930516663098619141338573830721124920904038776034277795234079574055686806025443322917639358678469701209374532240636560949471530471635324175738250760846611836658398673480966464958068548270810481578954133829570127483518899051874094070664031784274955134865756981617035911162257220992827360535829886021739388532224612679658415239817053469404532853536030575361479020544177288904911400338109310109420592624941563085220350869526725500363394675932151300377747315358268569855738681748034480107254689510658099497656412114249680019149090128345018628903226582985777485006142179576714857772465994201644583027813563039803318743275835226957384780742508710710398135670858534185835450056939020791998987049650662620316060631501316629648657227732008591016725081402751255624823446621989703650013317713648360278779373745668042244717647663376630039366244116712743767693265477674420982576388927149793828974129289738222671713663768387713714937515520694182225973277880797063633419655381139728698804541205052383268138656313853101208647279318715666923973360846657417241850264154211287163104094317585396428644191456115757787789674136514101178858767849529351091383559007137807410955651022079290917965870216909581691997838569338038253521477858205406443867160559475678574882189264605611107797745131374340495427706639360256000912001610995740917648237898950453074265309992911247209034798079134811208345219724661691370612437490357777727332990462576309065357224474918052361293291032480717681985295017994781678819330261142331141123491405092825984177303946268769076403470820151304606498132248357201330288263363981457585527445078395342850012476544447439841793393200546707336820740646131563714277709463041410284214554290647908022495920707952252619727643963122212974236749882990485528203350522147716299107304287871602589697, 844529322066961957944285014250322997859622900868205603790998624343014357527883606445480915476119531945875456960235830458455656013834428653388602531165683471677209343858149058029735559411076683107125507703377007696357580310681109367165705934812376577227763159394385009000853067498481754949210114128200377024154477080884318047378356469553461753634204195851181679633919680255369010715588684418101108830785472508169779062063339703536853793649574988855622444369980363636652313533622143280976685987949604663368756502789863964625819722434151841864942492453266857585551234299934520900444712599029848720956752545139766376453289713570246696267099411291472489660799018209309367526825270297547937163503760539744327693291765430630907590128372304955520008743742107102558976529069760925494927325342941123284700546610887318685689228745539721868333096928880248110438056501047030596315038354491106371976614258326597507092728377271658717422959305630714571892279466783018905788751805294252316517974511747954552910810344397277326085877951233406261337704413942436347687386263794483, 13573273614655496027830102976776581394383569509632662067836371834702418794177352243306722230861880704073472430606741694756446325121792034344850767972294923099506225897559863804366852825098473418647496255250334540064760435369812624773836357109331107696457264611472566149545506707635925610962137577449598278220934943047213366860234130750667363110124869957051622841461010486412098557161312556277280553326753903889785757774445406706960836401348064283013917081643247832455261656841573275194862349329409453789375904083240416047815125262274470351759684619895704667517544179730116097246566235420552993808826846651440284586012045202944442439894285958048742507519892201375204926896255444471288459854132613637719494401479960300056837047671379767251797649258030968418552664088362380776593877990550852855739321206422835194242989820920975330501203934989420769113334512698072597370011701734746708871451252034758526895892687574824029576654906510024605301092556338559807679812581102276849085676530033884748983571738507156364567503683910710732142298142774039009431248475228932757249748500224032733038406203446784535874204668164540569442516993080386340020705661928358189542723708545697618280729409157991780922712483617223590993412293354133341657915714714144225470748384664453838553288911635878941730389704827745577957275128009883740751436584141176374231845040917608999742995247507546888610327032478949486564228876246791033177100114666174931905369046757375074702589137514378163018560914487243226881053533463689751900194819918557276093427719235955446516555261926990897233111088507096243941090360919152869945600422410215875628070854398209558772110471701700958206600449313730212798373143273481123883618739375381308734590301495402099693707405481207611662228484456459495885596413482185523, 59923104495410530257643506359634157787265899298076885757810027052577558601833654377569492440802512007040037959957131119219596589604805540830949143546491374792589297808288495092100739867082031373151027650695001922946050227447487627157971036846942412387783503561528766079982415312826572101611785443208074712405, 11052923994698355021998761286706923307358485839185703291560957377342461448460582812300089014716351615254264235955950684105992795333504688594200006239872423926324819111094014625727003802563725957427584721821155072176771885115526893359220814285820144867407778653860666920667987234853659448955329648997231876764997360315923967145669101997875137415843070082960859342790734420315429938704619881028960458488004324084766440025234256868487908927515064454600475713446045174109756185089523974463131389105800522855557699360328130598390888663878150273289701952512158898273350549672479469677819978848167744215653227559234940271244286703654682292045254986934758729872034644860102799380069935973542098454799525224084590070567301495944387139924824668072246740710673455811894305394929179510687206324030496333196357235714279724151060432747841078785866910231944503019575103351077569834030021440156534411091352663744769685029283432391384459248515543536892924423521676957126575470140019198048535857863882315862258203241992206888250748958835968410144262367202713630698321758755851529851459971853136762241851300706765562403676584494384199086647663797396869858556349039201987987415336345787395009111176861966925801251172881594470678569686277558429513505764131484027113925981697851427515325686584609490696832518735792776323492657206785454832109595616246671660109065280102356385176480713344726396248176450386393663828246474363998812883095694391318175358009087002411981583066855855909908385423200701236341822648212126774538754396139952709149600320726280789919152701046314462496675626445485554121947151676029360747995324149386317674693257041516219345274937466127192124071328940634585961187134352463948704616848895019212191981929333380202610657433008803174655754659114414810894799853409180568013195795666483718072916750443886057845212900349313128987551121461640270153494517843261220623715520616285782876124307081375909958195036902537066439333522206345215181305062628735461226431686298450385172120944072643981957670836787139509023337287910322901985330325167961274802400955750788109409648895, 6197868487794264289879165981166817031873262771625116840299434536780248425800838822626226553449670121775591528506689897332590326277465390260823321880150146621077640283532863015493773364688572693661794676359188727139780879655312193001771555456857509528195778915937415283785871749485710642956254740267551504980540324777036246669968771986628817159532405411275002773761390942581788146915078208929581668847004625225993835430365800681313837890018602424336428533025426718651685191035032085877402127801948740800021650124203388018620928183650406932669328977356098756155011646410184371609357504302634390226057666378026099908352813831913986489532489505535026239000460309738361825872614674242108192117072114073217269525818942554153783334135707884978249293823728248758158160686915656347752014462959465299024747663955195552141892905446726254529181402309667094472374185367773426468996871276946996422844071274896522689759692752242061895578753058140801306651432348245386256567536750385826854318598789638070561658480925140667217414766580524886667139511180522025445967389135644007824368755887058426293983644494653961229182157633999134376738469721525380998640395837750125178425009038211059172462534919115882178169706788917879062767012732480594809844737973041140149871114206543691841763910457650825307275886186903331428541872330471300067942502792311164813530400213013120738401211888491967734190017238516506830337982259288260835741825434992533593430455756497225328044617815948263025576948485141304563957798865985413684198162751148328020798179429101460032756798062776868984271802813762858447874317690091990573469285356564237967140190790290613414899391107906136021516254823344967722600966342912446687830732605126002045219736338837832646526376650154691608305870308093826217434994397268437811506546306656162642540769124969450993403941893329326656635111955644215995444896625869764337786017220820891761247994743074089023170964112612048290705796122309682814941244821528646216241783398865433084368502204085406364438889434895, 688219715414337965043413904125347391897801099048447448557304502047891262547165952401994222109785251590101197582338396138499724096574505236935672475963810905718635022069053917335509642083375007422456457865722836444589945010481214211314547129924412828322434434708914655551959025859754223361973568437022533082777626930067352795763174619001869577286809667368361780658521821703434533875664690353157415021872149789167398656355308914109177140055310888235771934577406049879655739648987747439070323138118121608363997344507670834001172533481646842796931132821523326469000608392596261648110454876783229459742639747797973489533414233834300372007786061237220749161657315648195862275624451772922678771940239966808398634143969968807140277263427229213887251046862239104338116355166184241562729310236783506277144072859330895448749005403411091753766750333511592972597990856424402783150216027913192640401836500905118499738579186909317574200514153214305528602567399341468401541518820722199693308915969243988096860693501654479526758002396968979204518144090578592987800197702768021667646850957910401133271074149431827745498751378384826787457382452276419058103815693871477252333327380694424247956120533612899792715431234276374983801706277016140854344230586464524482310648025296250153937861740192732595433958790753392056069738419978392045576315754469220981657725795745528055148455977447706540974339571523238885130279412166607405162333833070020499917127162749990076419451332763915139263118257406826272298327049765305249474840499668376435260689854825231929010144263695388242026346810931242593289435258435531514042202344612929478911428880329420872329394011406550408712053776598844760897367913391115760844808893994252020026922098740476956064936683996043875412289119758019228891295813485991990348317832250783518751476110107118442417454560585714995090725057619301427454091907872788251075539750207664114524750882568520311873732002370657784969734322935532995249720340374009533079640712618889323912531829933321092493547034900043867416579768975646262057420138971859983252419576119379196844191801083616395451921441810216576108568472043614450774734312172860882980500243704387813036222110525558420607025496620487985319497540887205205, 316289861189083671309913007276676543786116492386926955722858314526839994417302529909439835531017470504333065556723299696080615448494949291378476077734452306145747876539088140668222630472913385894280754194596816334744941414725633309368057654447774437142825599640550963428444144857068327439537903533240583682174870988727368450959093693312395510804389690460518933429237877552342311435834444324435351581153316651910748540394080435539060287733981847085954956549596728212188432461412178075087982776015677478448649456407886362625455323559499504401390494917080639844090595240113570013895307085477973418495566956877951183189763588496039414610820462837147038738892949185032737010684280571552121728831570242377398774651641697593719326756937540967719918292046881456516441157619286926245413086501655598978028767751096719334268201749367996903274255592439035327876505332893134757099804504365453110764078593465314087942466967042802124006252286466690748662600101068912438723163475314976887356411333706984944549246295726283847304154429642263551218064030162110698277236555507389467143853107191585539903928217996506238510187929429686648353736474066208899582756513999368599517557984607226575312341731764438374434665517720653178245166467138508198128658617396585633916113246104522631928914594523086946590071127012847447908129905621728288590270834587755874589124523859177384650266319157800386312567156369528584893416179522445590252802278307596145267621346515231100311812455139663859413634585727162496106950026315011401060282069081686148516220314017792181611726322935587351731421765355029797644206992425072671314536865696312902485969476172579671498330644279444242243586787683905127423925175167874854235709425357399003902000383864021866545055902084243289806176634620153469970902442657464264402173625169230129057959695, 2780544244249711824309012909995940928929129698289783176799595433084621989279622865771905881836948144190901260166178572684269935019078334516657773579985609515748349732340644421514621779750340415043854986095066578299564528275365467253226592788409323488946464973046274848997033765339486806006205102658008154438401910003424781228966998327519720238637320806516926402807573114888763787234946962152353232860501331536159982848237224785519934767021617364891830724548921303049434156056538169958481191650236174028957348585922232936628676770819021008674295344031965840135699433588172865624060984797191368135073976520199257287790489132343051893005039967195624100987477434799881707134118551818549277140829072925316656435371830564647423661720819481672368297310065841841671261602387962874012515828667956574659660714456205169076388419140359738376400014340887724101472773834396573656540765806274061503231123728972114720639797639638779395489044331850807040706318465443303315717207199372985499030886597512177836661810775589855383410067931963982469722036110862041946657716619024335959130440531091798335729358479718413651067080513562580767655907736609073025401251768435965046704262937463171211750828605695]

def negativeWords : List Nat := pointWords ++ lineWords

def pairWords : List Nat := [
  8191,
  67100672,
  549688705024,
  4503049871556608,
  36888984547791732736,
  302194561415509874573312,
  2475577847115856892504571904,
  20279933723573099663397453037568,
  166133217063510832442551935283757056,
  1360963314184280739369385453844537802752,
  11149011469797627816914005637894453680144384,
  91332701960582167076159534185631364547742793728,
  748197494461089112687898904048692138375108966219776,
  91355004067076339167413824240109498970069278721,
  182710008134152678334827648480218997940138557442,
  365420016268305356669655296960437995880277114884,
  730840032536610713339310593920875991760554229768,
  1461680065073221426678621187841751983521108459536,
  2923360130146442853357242375683503967042216919072,
  5846720260292885706714484751367007934084433838144,
  11693440520585771413428969502734015868168867676288,
  23386881041171542826857939005468031736337735352576,
  46773762082343085653715878010936063472675470705152,
  93547524164686171307431756021872126945350941410304,
  187095048329372342614863512043744253890701882820608,
  374190096658744685229727024087488507781403765641216
]

def incidenceMask : Nat := 389515209005992732313513829080319019620122288333970


set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma pair_rows : ∀ p l : Fin 13,
    pairWords.map (fun a => a.testBit (p.val * 13 + l.val)) =
      List.ofFn (liftInput (edgeInput p l)) := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma mask_true : ∀ p l : Fin 13, I p l → incidenceMask.testBit (p.val * 13 + l.val) = true := by
  decide +kernel

lemma pointWords_length : pointWords.length = 13 := rfl
lemma lineWords_length : lineWords.length = 13 := rfl
lemma negativeWords_length : negativeWords.length = 26 := by simp [negativeWords, pointWords_length, lineWords_length]

lemma negative_point_lookup (p : Fin 13) : negativeWords.getD p.val 0 = pointWords.getD p.val 0 := by
  simp only [negativeWords, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (l₁ := pointWords) (l₂ := lineWords) (i := p.val) (by simpa only [pointWords_length] using p.isLt)]

lemma negative_line_lookup (l : Fin 13) : negativeWords.getD (13 + l.val) 0 = lineWords.getD l.val 0 := by
  simp only [negativeWords, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (l₁ := pointWords) (l₂ := lineWords) (i := 13 + l.val) (by simp only [pointWords_length]; omega),
    pointWords_length, Nat.add_sub_cancel_left]

lemma point_bits (r : Fin 8192) (p : Fin 13) :
    (pointWords.getD p.val 0).testBit r.val = r.val.testBit p.val := by
  rw [Q3PackedColumnCache.pointWords_spec]
  exact PackedColumns.col_testBit_lt 13 p.val r.val p.isLt r.isLt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma line_complement : ∀ l : Fin 13,
    lineWords.getD l.val 0 + PackedLineColumns.joinWords
      (List.ofFn (fun p => if I p l then pointWords.getD p.val 0 else 0)) + 1 =
        2 ^ (2 ^ 13) := by
  rw [Q3PackedColumnCache.power_13]
  decide +kernel

lemma negative_point_bits (r : Fin 8192) (p : Fin 13) :
    (negativeWords.getD p.val 0).testBit r.val = r.val.testBit p.val := by
  rw [negative_point_lookup]
  exact point_bits r p

lemma negative_line_bits (r : Fin 8192) (l : Fin 13) :
    (negativeWords.getD (13 + l.val) 0).testBit r.val =
      decide (∀ p : Fin 13, I p l → r.val.testBit p.val = false) := by
  rw [negative_line_lookup]
  exact PackedLineArithmetic.line_bits I (fun p => pointWords.getD p.val 0)
    r l _ (line_complement l) (point_bits r)

lemma positive_of_packed (C : Circuit) (hAO : IsAO2 26 C)
    (hpos : PackedEval.eval C pairWords = incidenceMask) :
    ∀ p l : Fin 13, I p l → circuitFun 26 C (liftInput (edgeInput p l)) = true := by
  intro p l hI
  have h := PackedEval.eval_testBit_of_isAO2 26 C pairWords (p.val * 13 + l.val) hAO
  rw [hpos, pair_rows p l] at h
  simpa [circuitFun] using h.symm.trans (mask_true p l hI)

lemma negative_of_packed (C : Circuit) (hAO : IsAO2 26 C)
    (hneg : PackedEval.eval C negativeWords = 0) :
    ∀ P : Finset (Fin 13), circuitFun 26 C (liftInput (independentInput I P)) = false := by
  exact PackedBoundary.independent_false_of_packed_zero I C hAO negativeWords
    negativeWords_length negative_point_bits negative_line_bits hneg

lemma exact_of_packed (C : Circuit) (hAO : IsAO2 26 C)
    (hpos : PackedEval.eval C pairWords = incidenceMask)
    (hneg : PackedEval.eval C negativeWords = 0) :
    ∀ z : Fin 26 → Bool, circuitFun 26 C z = decide (∃ p l : Fin 13,
      I p l ∧ z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true) := by
  exact ao2_exact_certificate I C hAO (positive_of_packed C hAO hpos)
    (fun P _ => negative_of_packed C hAO hneg P)


def canonicalC : Circuit := ⟨[
  { op := GateOp.or, inputs := [1, 4] },
  { op := GateOp.or, inputs := [26, 7] },
  { op := GateOp.or, inputs := [27, 10] },
  { op := GateOp.and, inputs := [28, 13] },
  { op := GateOp.or, inputs := [0, 4] },
  { op := GateOp.or, inputs := [30, 5] },
  { op := GateOp.or, inputs := [31, 6] },
  { op := GateOp.and, inputs := [32, 14] },
  { op := GateOp.or, inputs := [3, 4] },
  { op := GateOp.or, inputs := [34, 9] },
  { op := GateOp.or, inputs := [35, 11] },
  { op := GateOp.and, inputs := [36, 15] },
  { op := GateOp.or, inputs := [2, 4] },
  { op := GateOp.or, inputs := [38, 8] },
  { op := GateOp.or, inputs := [39, 12] },
  { op := GateOp.and, inputs := [40, 16] },
  { op := GateOp.or, inputs := [0, 1] },
  { op := GateOp.or, inputs := [42, 2] },
  { op := GateOp.or, inputs := [43, 3] },
  { op := GateOp.and, inputs := [44, 17] },
  { op := GateOp.or, inputs := [1, 6] },
  { op := GateOp.or, inputs := [46, 9] },
  { op := GateOp.or, inputs := [47, 12] },
  { op := GateOp.and, inputs := [48, 18] },
  { op := GateOp.or, inputs := [1, 5] },
  { op := GateOp.or, inputs := [50, 8] },
  { op := GateOp.or, inputs := [51, 11] },
  { op := GateOp.and, inputs := [52, 19] },
  { op := GateOp.or, inputs := [0, 10] },
  { op := GateOp.or, inputs := [54, 11] },
  { op := GateOp.or, inputs := [55, 12] },
  { op := GateOp.and, inputs := [56, 20] },
  { op := GateOp.or, inputs := [3, 6] },
  { op := GateOp.or, inputs := [58, 8] },
  { op := GateOp.or, inputs := [59, 10] },
  { op := GateOp.and, inputs := [60, 21] },
  { op := GateOp.or, inputs := [2, 5] },
  { op := GateOp.or, inputs := [62, 9] },
  { op := GateOp.or, inputs := [63, 10] },
  { op := GateOp.and, inputs := [64, 22] },
  { op := GateOp.or, inputs := [0, 7] },
  { op := GateOp.or, inputs := [66, 8] },
  { op := GateOp.or, inputs := [67, 9] },
  { op := GateOp.and, inputs := [68, 23] },
  { op := GateOp.or, inputs := [2, 6] },
  { op := GateOp.or, inputs := [70, 7] },
  { op := GateOp.or, inputs := [71, 11] },
  { op := GateOp.and, inputs := [72, 24] },
  { op := GateOp.or, inputs := [3, 5] },
  { op := GateOp.or, inputs := [74, 7] },
  { op := GateOp.or, inputs := [75, 12] },
  { op := GateOp.and, inputs := [76, 25] },
  { op := GateOp.or, inputs := [29, 33] },
  { op := GateOp.or, inputs := [78, 37] },
  { op := GateOp.or, inputs := [79, 41] },
  { op := GateOp.or, inputs := [80, 45] },
  { op := GateOp.or, inputs := [81, 49] },
  { op := GateOp.or, inputs := [82, 53] },
  { op := GateOp.or, inputs := [83, 57] },
  { op := GateOp.or, inputs := [84, 61] },
  { op := GateOp.or, inputs := [85, 65] },
  { op := GateOp.or, inputs := [86, 69] },
  { op := GateOp.or, inputs := [87, 73] },
  { op := GateOp.or, inputs := [88, 77] }
], 89⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma canonical_checks : IsAO2 26 canonicalC ∧ canonicalC.size = 64 ∧
    PackedEval.eval canonicalC pairWords = incidenceMask ∧
    PackedEval.eval canonicalC negativeWords = 0 := by decide +kernel

lemma canonical_exact : ∀ z : Fin 26 → Bool, circuitFun 26 canonicalC z =
    decide (∃ p l : Fin 13, I p l ∧ z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true) :=
  exact_of_packed canonicalC canonical_checks.1 canonical_checks.2.2.1 canonical_checks.2.2.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma plane_geometry :
    (∀ l : Fin 13, (Finset.univ.filter (fun p => I p l)).card = 4) ∧
    (∀ p p' : Fin 13, p ≠ p' → ∃! l : Fin 13, I p l ∧ I p' l) := by
  unfold I ExistsUnique
  decide +kernel

end Q3PackedCertificate


namespace ChunkedBoundary

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2583.ReducedCheck
open PEqualNP.Outside.L_meta_2583.CircuitCheckWrapper

def lowCode {a b : ℕ} (P : Finset (Fin (a + b))) : Fin (2 ^ a) :=
  PackedInputCode.code (fun p : Fin a => decide (Fin.castAdd b p ∈ P))

def highCode {a b : ℕ} (P : Finset (Fin (a + b))) : Fin (2 ^ b) :=
  PackedInputCode.code (fun p : Fin b => decide (Fin.natAdd a p ∈ P))

lemma input_bits {a b m : ℕ} (I : Fin (a + b) → Fin m → Prop) [DecidableRel I]
    (w : Fin (2 ^ b) → List ℕ) (hlen : ∀ h, (w h).length = a + b + m)
    (hlow : ∀ (h : Fin (2 ^ b)) (r : Fin (2 ^ a)) (p : Fin a),
      ((w h).getD p.val 0).testBit r.val = r.val.testBit p.val)
    (hhigh : ∀ (h : Fin (2 ^ b)) (r : Fin (2 ^ a)) (p : Fin b),
      ((w h).getD (a + p.val) 0).testBit r.val = h.val.testBit p.val)
    (hline : ∀ (h : Fin (2 ^ b)) (r : Fin (2 ^ a)) (l : Fin m),
      ((w h).getD (a + b + l.val) 0).testBit r.val = decide
        ((∀ p : Fin a, I (Fin.castAdd b p) l → r.val.testBit p.val = false) ∧
          (∀ p : Fin b, I (Fin.natAdd a p) l → h.val.testBit p.val = false)))
    (P : Finset (Fin (a + b))) :
    (w (highCode P)).map (fun v => v.testBit (lowCode P).val) =
      List.ofFn (liftInput (independentInput I P)) := by
  let high := highCode P
  let low := lowCode P
  have hwire : ∀ i : Fin (a + b + m), ((w high).getD i.val 0).testBit low.val =
      liftInput (independentInput I P) i := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro p
      refine Fin.addCases ?_ ?_ p
      · intro p
        simpa [low, lowCode, liftInput, independentInput] using
          (hlow high low p).trans
            (PackedInputCode.code_bit (fun p : Fin a => decide (Fin.castAdd b p ∈ P)) p)
      · intro p
        simpa [high, highCode, liftInput, independentInput] using
          (hhigh high low p).trans
            (PackedInputCode.code_bit (fun p : Fin b => decide (Fin.natAdd a p ∈ P)) p)
    · intro l
      have hwline : ((w high).getD (a + b + l.val) 0).testBit low.val =
          decide (l ∈ avoidingRight I P) := by
        rw [hline high low l]
        congr 1
        apply propext
        rw [mem_avoidingRight]
        constructor
        · intro h p
          refine Fin.addCases ?_ ?_ p
          · intro p hp hI
            have hf := h.1 p hI
            simp [low, lowCode, PackedInputCode.code_bit, hp] at hf
          · intro p hp hI
            have hf := h.2 p hI
            simp [high, highCode, PackedInputCode.code_bit, hp] at hf
        · intro h
          constructor
          · intro p hI
            have hp : Fin.castAdd b p ∉ P := fun hp => h _ hp hI
            simp [low, lowCode, PackedInputCode.code_bit, hp]
          · intro p hI
            have hp : Fin.natAdd a p ∉ P := fun hp => h _ hp hI
            simp [high, highCode, PackedInputCode.code_bit, hp]
      simpa [liftInput, independentInput] using hwline
  apply List.ext_getElem
  · simpa using hlen high
  · intro i hi hj
    have hwi : i < (w high).length := by simpa using hi
    have hib : i < a + b + m := by simpa [hlen high] using hwi
    simpa [List.getD_eq_getElem?_getD, hwi] using hwire ⟨i, hib⟩

lemma independent_false_of_chunks {a b m : ℕ} (I : Fin (a + b) → Fin m → Prop)
    [DecidableRel I] (C : Circuit) (hAO : IsAO2 (a + b + m) C)
    (w : Fin (2 ^ b) → List ℕ) (hlen : ∀ h, (w h).length = a + b + m)
    (hlow : ∀ (h : Fin (2 ^ b)) (r : Fin (2 ^ a)) (p : Fin a),
      ((w h).getD p.val 0).testBit r.val = r.val.testBit p.val)
    (hhigh : ∀ (h : Fin (2 ^ b)) (r : Fin (2 ^ a)) (p : Fin b),
      ((w h).getD (a + p.val) 0).testBit r.val = h.val.testBit p.val)
    (hline : ∀ (h : Fin (2 ^ b)) (r : Fin (2 ^ a)) (l : Fin m),
      ((w h).getD (a + b + l.val) 0).testBit r.val = decide
        ((∀ p : Fin a, I (Fin.castAdd b p) l → r.val.testBit p.val = false) ∧
          (∀ p : Fin b, I (Fin.natAdd a p) l → h.val.testBit p.val = false)))
    (hzero : ∀ h, PackedEval.eval C (w h) = 0) :
    ∀ P : Finset (Fin (a + b)),
      circuitFun (a + b + m) C (liftInput (independentInput I P)) = false := by
  intro P
  have h := PackedEval.eval_testBit_of_isAO2 (a + b + m) C (w (highCode P))
    (lowCode P).val hAO
  rw [hzero, input_bits I w hlen hlow hhigh hline P] at h
  simpa [circuitFun] using h.symm

end ChunkedBoundary


namespace Q3ChunkedCertificate

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open ReducedCheck CircuitCheckWrapper
open Q3PackedCertificate (I pairWords incidenceMask canonicalC)

def lowPointWords : List Nat := [
  119846208990821060515287012719268315574531798596153771515620054105155117203667308755138984881605024014080075919914262238439193179209611081661898287092982749585178595616576990184201479734164062746302055301390003845892100454894975254315942073693884824775567007123057532159964830625653144203223570886416149424810,
  143815450788985272618344415263121978689438158315384525818744064926186140644400770506166781857926028816896091103897114686127031815051533297994277944511579299502214314739892388221041775680996875295562466361668004615070520545873970305179130488432661789730680408547669038591957796750783773043868285063699379309772,
  169194647987041497198052253250731739634633127429864148022051841089630753699295024124902096303442386843407166004584840807208272723590039174110915228837152117061428605576343986142402089036466912112426431013727064253024141818675259182563682927567837399683153421820787104225832702059745615345727394192587505070320,
  179069821994067265517004719393770557123035839147560499073922571114317373565012632536861362624654977515201358572945823733699027940920197102560968646862666832065013932750060561209079253766221790251284004808302573839776523636885877422791135238515376547524582609864801915756523326693582908070186191519003118206720,
  179766570466052360237648572536963127610949142151705149077185617265867657072940646045213890928808158455225716514812268414598264282604049739409665520460023745597470080465874001603182053859457467143941243028332742390810947146161643764595180884270010128854499581430719252352917935056902309958553029775825154539520,
  179769313444375785814462265863485611229889718115776549548420631039577310219318555512504201030636628662239812719543346771400604958784932998973090366819193438631844709885019339289485527600645229101680144570744617427323613239093066544488844122372018577072445227788470567772585250041087614243742592599359351685120,
  179769313486231590763185205067502474281972610037491134208877555181135709923949037735690276024213413705823039792595812100825199281213020878487102478859428781160318831728534053767098825058678708531551206723464342007537350133167915838047987720003371153224504147359993809275143228500884134199151686065190149816320,
  179769313486231590772930519078902473361269403363094992027077741372816159198983668324764656509214724291581902479869920821760871587342679845464593386307578492764517105656857966598509267284159204378328176331317696638943488431251920295735812264550083217605459765810970935573515804682568218669795142748890432798720,
  179769313486231590772930519078902473361797697894230657273430081157732675805499410614616176613472387041631651377316136471641673072203277570454821379686787760899244944958633938372376730076395090525612731964434268678008150116831451773765893368201788358737656950422124978427902852027528247743196825908506284523520,
  179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474110969959963482268385702277221395399966640087262359691628045276706960578432807926936308666529070259922820652728111753896392184596904358265409895975218053120
]

def lowLineWords : List Nat := [
  1612202362438516399445625478482434675121823726883503404772301843350203396559111756406055148913550443347281823494806389103104468523147286808346284746286493861864005434387625707294085024003364773297834340878416831890049116906832362379820380108676007858279181472248627,
  11540594032658607306566862601501305269438134594985383637573631145613154769671340896777851149190755077723567764553128464542387995665915090527196023934338072556743923144455916925710573989989925907747028471236585529682186524614830995187538005219136435186722779142022605140153685,
  796045880515921893740840784340009919099334674736111188786015696109986287490171558823122061988264889467792355759382783138912642201399201885270835455,
  1393481448109428024177612725692000257830902900038233105088416187017886575689496888172687782322825188039705927097314219305260869837098837594210872808275440014594128991381499292894772743965303669543108482905900987801709156765455,
  2743103890840491199709018373066338191222975477137875292186313895746283296032669003322018422559052964387275713433606368469654227036154980125014838340420754167662590881587937518521434647154132816349326054048752662986772727280727288952070086374316429955952552234448558758525173509399247979016332590671003649,
  145367744859121378101984360338322011028699661524619071311737937905421215472927008112205736097024724415912224248215020537264825714291507,
  72294757326097933040861497784880691502824544888109615384531391835929546202845673426460479344206140712111202128718028925208414114298998390254824122401745389029896603612666735780901582145914989584815640143462939230781780787,
  59923104495410530257643506359634157787265899298076885757810027052577558601833654377569492440802512007040037959957131119219596589604805540830949143546491374792589297808288495092100739867082031373151027650695001922946050227447487627157971036846942412387783503561528766079982415312826572101611785443208074712405,
  327479277917408467359118278243034488056076247630130719693098679591209568603539525136273912089569344449019920319495285561697522348095392811331331240221415944707369595257330459289632194594578979695157867955814655,
  183632267622891382779718862777337890176768437789250849134046269477221477242087806515921312485605712698371734994876781313363032641283387305168655,
  113427455640312821154458202477256070485,
  1684641406969115364874486225963184091504279981394597057304974334423198082012594085395335671627782269635974753234311105849883066826689934540267397107598739745340130446522310749429691706754229252102351376690654656563612029603792517803755816029321629455,
  478611500756798850801714011323471660170568768659788346620398081151254972618377633362909867462188365193808315833746849196845099826791196907804893604951762174510088758215373707240627875944495525099088412524971307892190284093278822273880968004004958098409062655
]

def allOnes : Nat := 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137215

lemma lowPointWords_spec (p : Fin 10) :
    lowPointWords.getD p.val 0 = PackedColumns.col 10 p.val := by
  fin_cases p
  · exact Q3PackedColumnCache.col_10_0.symm
  · exact Q3PackedColumnCache.col_10_1.symm
  · exact Q3PackedColumnCache.col_10_2.symm
  · exact Q3PackedColumnCache.col_10_3.symm
  · exact Q3PackedColumnCache.col_10_4.symm
  · exact Q3PackedColumnCache.col_10_5.symm
  · exact Q3PackedColumnCache.col_10_6.symm
  · exact Q3PackedColumnCache.col_10_7.symm
  · exact Q3PackedColumnCache.col_10_8.symm
  · exact Q3PackedColumnCache.col_10_9.symm

lemma low_point_bits (r : Fin 1024) (p : Fin 10) :
    (lowPointWords.getD p.val 0).testBit r.val = r.val.testBit p.val := by
  rw [lowPointWords_spec]
  exact PackedColumns.col_testBit_lt 10 p.val r.val p.isLt r.isLt

lemma allOnes_spec : allOnes = 2 ^ (2 ^ 10) - 1 := by
  rw [Q3PackedColumnCache.power_10]
  rfl

lemma allOnes_bits (r : Fin 1024) : allOnes.testBit r.val = true := by
  rw [allOnes_spec, Nat.testBit_two_pow_sub_one]
  simp [r.isLt]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma low_line_complement : ∀ l : Fin 13,
    lowLineWords.getD l.val 0 + PackedLineColumns.joinWords
      (List.ofFn (fun p : Fin 10 => if I (Fin.castAdd 3 p) l
        then lowPointWords.getD p.val 0 else 0)) + 1 = 2 ^ (2 ^ 10) := by
  rw [Q3PackedColumnCache.power_10]
  decide +kernel

lemma low_line_bits (r : Fin 1024) (l : Fin 13) :
    (lowLineWords.getD l.val 0).testBit r.val =
      decide (∀ p : Fin 10, I (Fin.castAdd 3 p) l → r.val.testBit p.val = false) := by
  exact PackedLineArithmetic.line_bits (fun p : Fin 10 => I (Fin.castAdd 3 p))
    (fun p => lowPointWords.getD p.val 0) r l _ (low_line_complement l) (low_point_bits r)

def data (h : Fin 8) (i : Fin 26) : Nat :=
  Fin.addCases (motive := fun _ => Nat)
    (fun p : Fin 13 => Fin.addCases (motive := fun _ => Nat)
      (fun p : Fin 10 => lowPointWords.getD p.val 0)
      (fun p : Fin 3 => if h.val.testBit p.val then allOnes else 0) p)
    (fun l : Fin 13 => if ∀ p : Fin 3,
        I (Fin.natAdd 10 p) l → h.val.testBit p.val = false
      then lowLineWords.getD l.val 0 else 0) i

def words (h : Fin 8) : List Nat := List.ofFn (data h)

lemma words_length (h : Fin 8) : (words h).length = 26 := by simp [words]

lemma words_getD (h : Fin 8) (i : Fin 26) : (words h).getD i.val 0 = data h i := by
  simp only [words, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    i.isLt, dite_eq_left, Option.getD_some]

lemma low_lookup (h : Fin 8) (p : Fin 10) :
    (words h).getD p.val 0 = lowPointWords.getD p.val 0 := by
  simpa [data] using words_getD h (Fin.castAdd 13 (Fin.castAdd 3 p))

lemma high_lookup (h : Fin 8) (p : Fin 3) :
    (words h).getD (10 + p.val) 0 = if h.val.testBit p.val then allOnes else 0 := by
  simpa [data] using words_getD h (Fin.castAdd 13 (Fin.natAdd 10 p))

lemma line_lookup (h : Fin 8) (l : Fin 13) :
    (words h).getD (13 + l.val) 0 = if ∀ p : Fin 3,
        I (Fin.natAdd 10 p) l → h.val.testBit p.val = false
      then lowLineWords.getD l.val 0 else 0 := by
  have hw := words_getD h (Fin.natAdd 13 l)
  simp only [data, Fin.addCases_right] at hw
  exact hw

lemma low_bits (h : Fin 8) (r : Fin 1024) (p : Fin 10) :
    ((words h).getD p.val 0).testBit r.val = r.val.testBit p.val := by
  rw [low_lookup]
  exact low_point_bits r p

lemma high_bits (h : Fin 8) (r : Fin 1024) (p : Fin 3) :
    ((words h).getD (10 + p.val) 0).testBit r.val = h.val.testBit p.val := by
  rw [high_lookup]
  cases h.val.testBit p.val <;> simp [allOnes_bits r]

lemma line_bits (h : Fin 8) (r : Fin 1024) (l : Fin 13) :
    ((words h).getD (13 + l.val) 0).testBit r.val = decide
      ((∀ p : Fin 10, I (Fin.castAdd 3 p) l → r.val.testBit p.val = false) ∧
        (∀ p : Fin 3, I (Fin.natAdd 10 p) l → h.val.testBit p.val = false)) := by
  rw [line_lookup]
  split
  · rename_i hh
    rw [low_line_bits r l]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact (and_iff_left hh).symm
  · rename_i hh
    simp [hh]

lemma negative_of_chunks (C : Circuit) (hAO : IsAO2 26 C)
    (hneg : ∀ h : Fin 8, PackedEval.eval C (words h) = 0) :
    ∀ P : Finset (Fin 13), circuitFun 26 C (liftInput (independentInput I P)) = false := by
  exact ChunkedBoundary.independent_false_of_chunks (a := 10) (b := 3)
    I C hAO words words_length low_bits high_bits line_bits hneg

lemma exact_of_chunks (C : Circuit) (hAO : IsAO2 26 C)
    (hpos : PackedEval.eval C pairWords = incidenceMask)
    (hneg : ∀ h : Fin 8, PackedEval.eval C (words h) = 0) :
    ∀ z : Fin 26 → Bool, circuitFun 26 C z = decide (∃ p l : Fin 13,
      I p l ∧ z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true) := by
  exact ao2_exact_certificate I C hAO (Q3PackedCertificate.positive_of_packed C hAO hpos)
    (fun P _ => negative_of_chunks C hAO hneg P)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma canonical_checks : IsAO2 26 canonicalC ∧ canonicalC.size = 64 ∧
    PackedEval.eval canonicalC pairWords = incidenceMask ∧
    (∀ h : Fin 8, PackedEval.eval canonicalC (words h) = 0) := by decide +kernel

lemma canonical_exact : ∀ z : Fin 26 → Bool, circuitFun 26 canonicalC z =
    decide (∃ p l : Fin 13, I p l ∧ z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true) :=
  exact_of_chunks canonicalC canonical_checks.1 canonical_checks.2.2.1 canonical_checks.2.2.2

end Q3ChunkedCertificate

namespace SingleUse

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hC : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [ite_eq_left (hC j hj i hi)]

lemma wv_missing (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (w : ℕ) (hw : n + C.gates.length ≤ w) : wv n C x w = false := by
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wires_eq, foldl_len, List.length_ofFn]
  unfold wv
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega)]
  rfl


end SingleUse

namespace MintermCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse

lemma gate_mem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  exact List.getElem_mem hk

lemma inputs_two (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (k : ℕ) (hk : k < C.gates.length) :
    (gateAt C k).inputs = [opnd C k 0, opnd C k 1] := by
  obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gate_mem C k hk))
  simp [opnd, hin]

lemma opnd_back (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (k : ℕ) (hk : k < C.gates.length) (b : Fin 2) : opnd C k b < n + k := by
  apply hAO.2.1 k hk
  rw [inputs_two n C hAO k hk]
  fin_cases b <;> simp


end MintermCircuit

namespace AndSignature

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.MintermCircuit

def isAnd (C : Circuit) (k : ℕ) : Bool :=
  match (gateAt C k).op with
  | GateOp.and => true
  | _ => false

def andPrefix (C : Circuit) (r : ℕ) : Finset ℕ :=
  (Finset.range r).filter (fun k => isAnd C k = true)

lemma false_join_of_signature_eq (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (r : ℕ) (hr : r ≤ C.gates.length) (x y : Fin n → Bool)
    (hsig : ∀ k < r, (gateAt C k).op = GateOp.and →
      wv n C x (opnd C k 0) = wv n C y (opnd C k 0)) :
    ∀ w, w < n + r → wv n C x w = false → wv n C y w = false →
      wv n C (fun i => x i || y i) w = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hx hy
    by_cases hwn : w < n
    · rw [wv_input n C x w hwn] at hx
      rw [wv_input n C y w hwn] at hy
      rw [wv_input n C _ w hwn]
      simp [hx, hy]
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hkr : k < r := by omega
      have hk : k < C.gates.length := by omega
      have ha := opnd_back n C hAO k hk 0
      have hb := opnd_back n C hAO k hk 1
      rw [wv_rec n C x hAO.2.1 k hk, inputs_two n C hAO k hk] at hx
      rw [wv_rec n C y hAO.2.1 k hk, inputs_two n C hAO k hk] at hy
      rw [wv_rec n C _ hAO.2.1 k hk, inputs_two n C hAO k hk]
      rcases hAO.1 _ (gate_mem C k hk) with hop | hop
      · have heq := hsig k hkr hop
        cases hl : wv n C x (opnd C k 0) with
        | false =>
          have hly : wv n C y (opnd C k 0) = false := heq.symm.trans hl
          have hj := ih _ ha (by omega) hl hly
          simp [hop, GateOp.eval, hj]
        | true =>
          have hly : wv n C y (opnd C k 0) = true := heq.symm.trans hl
          have hxr : wv n C x (opnd C k 1) = false := by
            simpa [hop, GateOp.eval, hl] using hx
          have hyr : wv n C y (opnd C k 1) = false := by
            simpa [hop, GateOp.eval, hly] using hy
          have hj := ih _ hb (by omega) hxr hyr
          simp [hop, GateOp.eval, hj]
      · have hxx : wv n C x (opnd C k 0) = false ∧
            wv n C x (opnd C k 1) = false := by simpa [hop, GateOp.eval] using hx
        have hyy : wv n C y (opnd C k 0) = false ∧
            wv n C y (opnd C k 1) = false := by simpa [hop, GateOp.eval] using hy
        have hj0 := ih _ ha (by omega) hxx.1 hyy.1
        have hj1 := ih _ hb (by omega) hxx.2 hyy.2
        simp [hop, GateOp.eval, hj0, hj1]

lemma false_family_card_le_signatures {α : Type} [Fintype α]
    (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (r : ℕ) (hr : r ≤ C.gates.length) (w : ℕ) (hw : w < n + r)
    (f : α → Fin n → Bool)
    (hfalse : ∀ a, wv n C (f a) w = false)
    (hjoin : ∀ a b, a ≠ b → wv n C (fun i => f a i || f b i) w = true) :
    Fintype.card α ≤ 2 ^ (andPrefix C r).card := by
  classical
  let sig : α → ((andPrefix C r) → Bool) := fun a k => wv n C (f a) (opnd C k.val 0)
  have hinj : Function.Injective sig := by
    intro a b hab
    by_contra hne
    have heq : ∀ k < r, (gateAt C k).op = GateOp.and →
        wv n C (f a) (opnd C k 0) = wv n C (f b) (opnd C k 0) := by
      intro k hk hop
      have hkA : k ∈ andPrefix C r := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_range.mpr hk, by simp [isAnd, hop]⟩
      exact congrFun hab ⟨k, hkA⟩
    have hf := false_join_of_signature_eq n C hAO r hr (f a) (f b) heq w hw
      (hfalse a) (hfalse b)
    rw [hjoin a b hne] at hf
    cases hf
  have hcard := Fintype.card_le_of_injective sig hinj
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] using hcard

lemma false_cube_le_and_count (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (r : ℕ) (hr : r ≤ C.gates.length) (w : ℕ) (hw : w < n + r)
    (d : ℕ) (f : (Fin d → Bool) → Fin n → Bool)
    (hfalse : ∀ a, wv n C (f a) w = false)
    (hjoin : ∀ a b, a ≠ b → wv n C (fun i => f a i || f b i) w = true) :
    d ≤ (andPrefix C r).card := by
  have hc := false_family_card_le_signatures n C hAO r hr w hw f hfalse hjoin
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

end AndSignature

namespace ThetaFalseFamily

def edges : List (Fin 8 × Fin 8) :=
  [(0, 2), (0, 3), (0, 4), (2, 5), (3, 6), (4, 7), (5, 1), (6, 1), (7, 1)]

def graphFun (x : Fin 8 → Bool) : Bool :=
  edges.any (fun e => x e.1 && x e.2)

def masks : List Nat := [3, 30, 56, 84, 112, 140, 168, 196, 225]

def falseInput (i : Fin 9) (v : Fin 8) : Bool :=
  (masks.getD i.val 0).testBit v.val

lemma false_inputs : ∀ i : Fin 9, graphFun (falseInput i) = false := by
  decide +kernel

lemma distinct_union_true : ∀ i j : Fin 9, i ≠ j →
    graphFun (fun v => falseInput i v || falseInput j v) = true := by
  decide +kernel

lemma falseInput_injective : Function.Injective falseInput := by
  intro i j hij
  by_contra hne
  have ht := distinct_union_true i j hne
  have ht' : graphFun (falseInput j) = true := by
    simpa only [hij, Bool.or_self] using ht
  rw [false_inputs j] at ht'
  cases ht'

lemma graphFun_eq_true (x : Fin 8 → Bool) :
    graphFun x = true ↔ ∃ p q : Fin 8, (p, q) ∈ edges ∧ x p = true ∧ x q = true := by
  simp only [graphFun, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨p, q⟩, hmem, hp, hq⟩
    exact ⟨p, q, hmem, hp, hq⟩
  · rintro ⟨p, q, hmem, hp, hq⟩
    exact ⟨(p, q), hmem, hp, hq⟩

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity

def canonicalC : Circuit := ⟨[
  ⟨.or, [2, 3]⟩,
  ⟨.or, [8, 4]⟩,
  ⟨.and, [0, 9]⟩,
  ⟨.or, [1, 2]⟩,
  ⟨.and, [5, 11]⟩,
  ⟨.or, [1, 3]⟩,
  ⟨.and, [6, 13]⟩,
  ⟨.or, [1, 4]⟩,
  ⟨.and, [7, 15]⟩,
  ⟨.or, [10, 12]⟩,
  ⟨.or, [14, 16]⟩,
  ⟨.or, [17, 18]⟩], 19⟩

lemma canonical_checks : IsAO2 8 canonicalC ∧ canonicalC.size = 12 ∧
    (canonicalC.gates.filter (fun g => match g.op with | .and => true | _ => false)).length = 4 ∧
    (canonicalC.gates.filter (fun g => match g.op with | .or => true | _ => false)).length = 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma canonical_exact : ∀ x : Fin 8 → Bool, canonicalC.eval (List.ofFn x) = graphFun x := by
  decide +kernel

end ThetaFalseFamily

namespace ThetaAndBound
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2583.SingleUse
open PEqualNP.Outside.L_meta_2583.AndSignature
open PEqualNP.Outside.L_meta_2583.ThetaFalseFamily

lemma and_count_ge_four (C : Circuit) (hAO : IsAO2 8 C)
    (hcompute : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graphFun x) :
    4 ≤ (andPrefix C C.gates.length).card := by
  have hvalid : C.output < 8 + C.gates.length := by
    by_contra hbad
    have hf := wv_missing 8 C (fun v => falseInput 0 v || falseInput 1 v)
      C.output (by omega)
    change C.eval (List.ofFn _) = false at hf
    rw [hcompute, distinct_union_true 0 1 (by decide)] at hf
    cases hf
  have hc := false_family_card_le_signatures 8 C hAO C.gates.length le_rfl
    C.output hvalid falseInput
    (fun i => by
      change C.eval (List.ofFn _) = false
      rw [hcompute]
      exact false_inputs i)
    (fun i j hij => by
      change C.eval (List.ofFn _) = true
      rw [hcompute]
      exact distinct_union_true i j hij)
  simp only [Fintype.card_fin] at hc
  by_contra hsmall
  have hk : (andPrefix C C.gates.length).card ≤ 3 := by omega
  have hp : 2 ^ (andPrefix C C.gates.length).card ≤ 2 ^ 3 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mpr hk
  norm_num at hp
  omega

lemma canonical_and_count : (andPrefix canonicalC canonicalC.gates.length).card = 4 := by
  decide +kernel

lemma exact_and_complexity_four :
    (∃ C : Circuit, IsAO2 8 C ∧
      (∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graphFun x) ∧
      (andPrefix C C.gates.length).card = 4 ∧ C.size = 12) ∧
    (∀ C : Circuit, IsAO2 8 C →
      (∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graphFun x) →
      4 ≤ (andPrefix C C.gates.length).card) := by
  exact ⟨⟨canonicalC, canonical_checks.1, canonical_exact, canonical_and_count,
    canonical_checks.2.1⟩, and_count_ge_four⟩

end ThetaAndBound

namespace AndPairSeparation
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.MintermCircuit
  PEqualNP.Outside.L_meta_2583.AndSignature

def crossedAt (n : ℕ) (C : Circuit) (x y : Fin n → Bool) (k : ℕ) : Prop :=
  (wv n C x (opnd C k 0) = false ∧ wv n C x (opnd C k 1) = true ∧
   wv n C y (opnd C k 0) = true ∧ wv n C y (opnd C k 1) = false) ∨
  (wv n C x (opnd C k 0) = true ∧ wv n C x (opnd C k 1) = false ∧
   wv n C y (opnd C k 0) = false ∧ wv n C y (opnd C k 1) = true)

lemma false_join_of_no_crossed_and (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (r : ℕ) (hr : r ≤ C.gates.length) (x y : Fin n → Bool)
    (hnocross : ∀ k < r, (gateAt C k).op = .and → ¬ crossedAt n C x y k) :
    ∀ w, w < n + r → wv n C x w = false → wv n C y w = false →
      wv n C (fun i => x i || y i) w = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hx hy
    by_cases hwn : w < n
    · rw [wv_input n C x w hwn] at hx
      rw [wv_input n C y w hwn] at hy
      rw [wv_input n C _ w hwn]
      simp [hx, hy]
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hkr : k < r := by omega
      have hk : k < C.gates.length := by omega
      have ha := opnd_back n C hAO k hk 0
      have hb := opnd_back n C hAO k hk 1
      rw [wv_rec n C x hAO.2.1 k hk, inputs_two n C hAO k hk] at hx
      rw [wv_rec n C y hAO.2.1 k hk, inputs_two n C hAO k hk] at hy
      rw [wv_rec n C _ hAO.2.1 k hk, inputs_two n C hAO k hk]
      rcases hAO.1 _ (gate_mem C k hk) with hop | hop
      · by_cases hl : wv n C x (opnd C k 0) = false ∧
            wv n C y (opnd C k 0) = false
        · have hj := ih _ ha (by omega) hl.1 hl.2
          simp [hop, GateOp.eval, hj]
        · have hright : wv n C x (opnd C k 1) = false ∧
              wv n C y (opnd C k 1) = false := by
            have hn := hnocross k hkr hop
            unfold crossedAt at hn
            cases hxl : wv n C x (opnd C k 0) <;>
              cases hxr : wv n C x (opnd C k 1) <;>
              cases hyl : wv n C y (opnd C k 0) <;>
              cases hyr : wv n C y (opnd C k 1) <;>
              simp_all [GateOp.eval]
          have hj := ih _ hb (by omega) hright.1 hright.2
          simp [hop, GateOp.eval, hj]
      · have hxx : wv n C x (opnd C k 0) = false ∧
            wv n C x (opnd C k 1) = false := by simpa [hop, GateOp.eval] using hx
        have hyy : wv n C y (opnd C k 0) = false ∧
            wv n C y (opnd C k 1) = false := by simpa [hop, GateOp.eval] using hy
        have hj0 := ih _ ha (by omega) hxx.1 hyy.1
        have hj1 := ih _ hb (by omega) hxx.2 hyy.2
        simp [hop, GateOp.eval, hj0, hj1]

lemma exists_crossed_and_prefix (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (r : ℕ) (hr : r ≤ C.gates.length) (w : ℕ) (hw : w < n + r)
    (x y : Fin n → Bool) (hx : wv n C x w = false) (hy : wv n C y w = false)
    (hj : wv n C (fun i => x i || y i) w = true) :
    ∃ k < r, (gateAt C k).op = .and ∧ crossedAt n C x y k := by
  by_contra hn
  have hnocross : ∀ k < r, (gateAt C k).op = .and → ¬ crossedAt n C x y k := by
    intro k hk hop hcross
    exact hn ⟨k, hk, hop, hcross⟩
  have hf := false_join_of_no_crossed_and n C hAO r hr x y hnocross w hw hx hy
  rw [hj] at hf
  cases hf

lemma exists_crossed_and (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool)
    (hx : C.eval (List.ofFn x) = false) (hy : C.eval (List.ofFn y) = false)
    (hj : C.eval (List.ofFn (fun i => x i || y i)) = true) :
    ∃ k < C.gates.length, (gateAt C k).op = .and ∧ crossedAt n C x y k := by
  have hw : C.output < n + C.gates.length := by
    by_contra hbad
    have hf := wv_missing n C (fun i => x i || y i) C.output (by omega)
    change C.eval (List.ofFn _) = false at hf
    rw [hj] at hf
    cases hf
  exact exists_crossed_and_prefix n C hAO C.gates.length le_rfl C.output hw x y hx hy hj

def choiceAt (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) : Option Bool :=
  match wv n C x (opnd C k 0), wv n C x (opnd C k 1) with
  | false, true => some false
  | true, false => some true
  | _, _ => none

lemma choiceAt_forced_iff (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) :
    choiceAt n C x k ≠ none ↔
      wv n C x (opnd C k 0) ≠ wv n C x (opnd C k 1) := by
  unfold choiceAt
  cases wv n C x (opnd C k 0) <;> cases wv n C x (opnd C k 1) <;> simp

lemma crossed_choices (n : ℕ) (C : Circuit) (x y : Fin n → Bool) (k : ℕ)
    (hc : crossedAt n C x y k) :
    ∃ b c : Bool, choiceAt n C x k = some b ∧ choiceAt n C y k = some c ∧ b ≠ c := by
  rcases hc with ⟨hxl, hxr, hyl, hyr⟩ | ⟨hxl, hxr, hyl, hyr⟩
  · exact ⟨false, true, by simp [choiceAt, hxl, hxr], by simp [choiceAt, hyl, hyr], by decide⟩
  · exact ⟨true, false, by simp [choiceAt, hxl, hxr], by simp [choiceAt, hyl, hyr], by decide⟩

end AndPairSeparation

namespace AndChoiceBridge
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2583.AndSignature
open PEqualNP.Outside.L_meta_2583.AndPairSeparation

def gateChoices (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (andPrefix C C.gates.length) → Option Bool :=
  fun k => choiceAt n C x k.val

lemma family_choices_separate {α : Type} (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (f : α → Fin n → Bool)
    (hfalse : ∀ a, C.eval (List.ofFn (f a)) = false)
    (hjoin : ∀ a b, a ≠ b → C.eval (List.ofFn (fun i => f a i || f b i)) = true) :
    ∀ a b, a ≠ b → ∃ k u v,
      gateChoices n C (f a) k = some u ∧ gateChoices n C (f b) k = some v ∧ u ≠ v := by
  intro a b hab
  obtain ⟨k, hk, hop, hc⟩ := exists_crossed_and n C hAO (f a) (f b)
    (hfalse a) (hfalse b) (hjoin a b hab)
  have hkA : k ∈ andPrefix C C.gates.length := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr hk, by simp [isAnd, hop]⟩
  obtain ⟨u, v, hu, hv, huv⟩ := crossed_choices n C (f a) (f b) k hc
  exact ⟨⟨k, hkA⟩, u, v, hu, hv, huv⟩

end AndChoiceBridge

namespace ChoiceSubcube

variable {α K : Type*}

def Compatible (p : K → Option Bool) (s : K → Bool) : Prop :=
  ∀ k b, p k = some b → s k = b

noncomputable def choiceSet [Fintype K] (p : K → Option Bool) : Finset (K → Bool) := by
  classical
  exact Finset.univ.filter (Compatible p)

noncomputable def forcedCount [Fintype K] (p : K → Option Bool) : Nat := by
  classical
  exact Fintype.card {k : K // p k ≠ none}

noncomputable def compatibleEquiv (p : K → Option Bool) :
    {s : K → Bool // Compatible p s} ≃ ({k : K // p k = none} → Bool) := by
  classical
  refine {
    toFun := fun s k => s.val k.val
    invFun := fun t => ⟨fun k => if h : p k = none then t ⟨k, h⟩ else (p k).getD false, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro k b hb
    simp [hb]
  · intro s
    apply Subtype.ext
    funext k
    cases hp : p k with
    | none => simp [hp]
    | some b => simpa [hp] using (s.property k b hp).symm
  · intro t
    funext k
    simp [k.property]

lemma choiceSet_card [Fintype K] (p : K → Option Bool) :
    (choiceSet p).card = 2 ^ (Fintype.card K - forcedCount p) := by
  classical
  have hm (s : K → Bool) : s ∈ choiceSet p ↔ Compatible p s := by
    simp [choiceSet]
  let e : (choiceSet p : Set (K → Bool)) ≃ {s : K → Bool // Compatible p s} :=
    Equiv.subtypeEquivRight hm
  have hfree : Fintype.card {k : K // p k = none} =
      Fintype.card K - forcedCount p := by
    simpa only [not_not, forcedCount] using
      (Fintype.card_subtype_compl (fun k : K => p k ≠ none))
  calc
    (choiceSet p).card = Fintype.card {s : K → Bool // Compatible p s} := by
      rw [← Fintype.card_coe (choiceSet p)]
      exact Fintype.card_congr e
    _ = Fintype.card ({k : K // p k = none} → Bool) :=
      Fintype.card_congr (compatibleEquiv p)
    _ = 2 ^ (Fintype.card K - forcedCount p) := by
      rw [Fintype.card_fun, Fintype.card_bool, hfree]

lemma disjoint_of_opposite [Fintype K] (p q : K → Option Bool)
    (h : ∃ k x y, p k = some x ∧ q k = some y ∧ x ≠ y) :
    Disjoint (choiceSet p) (choiceSet q) := by
  classical
  apply Finset.disjoint_left.mpr
  intro s hs ht
  have hp : Compatible p s := by simpa [choiceSet] using hs
  have hq : Compatible q s := by simpa [choiceSet] using ht
  obtain ⟨k, x, y, hx, hy, hxy⟩ := h
  exact hxy ((hp k x hx).symm.trans (hq k y hy))

lemma sum_choiceSet_card [Fintype α] [Fintype K] (p : α → K → Option Bool)
    (hsep : ∀ a b, a ≠ b → ∃ k x y, p a k = some x ∧ p b k = some y ∧ x ≠ y) :
    ∑ a, (choiceSet (p a)).card ≤ 2 ^ Fintype.card K := by
  classical
  have hd : (↑(Finset.univ : Finset α) : Set α).PairwiseDisjoint
      (fun a => choiceSet (p a)) := by
    intro a ha b hb hab
    exact disjoint_of_opposite (p a) (p b) (hsep a b hab)
  calc
    (∑ a, (choiceSet (p a)).card) =
        ((Finset.univ : Finset α).biUnion (fun a => choiceSet (p a))).card := by
      simpa using (Finset.card_biUnion hd).symm
    _ ≤ Fintype.card (K → Bool) := by
      simpa using Finset.card_le_card
        (Finset.subset_univ ((Finset.univ : Finset α).biUnion (fun a => choiceSet (p a))))
    _ = 2 ^ Fintype.card K := by rw [Fintype.card_fun, Fintype.card_bool]

lemma sum_capacity [Fintype α] [Fintype K] (p : α → K → Option Bool)
    (hsep : ∀ a b, a ≠ b → ∃ k x y, p a k = some x ∧ p b k = some y ∧ x ≠ y) :
    ∑ a, 2 ^ (Fintype.card K - forcedCount (p a)) ≤ 2 ^ Fintype.card K := by
  simpa only [choiceSet_card] using sum_choiceSet_card p hsep

def forcedSet [Fintype K] (p : K → Option Bool) : Finset K :=
  Finset.univ.filter (fun k => p k ≠ none)

lemma forcedCount_eq_card [Fintype K] (p : K → Option Bool) :
    forcedCount p = (forcedSet p).card := by
  classical
  let e : (forcedSet p : Set K) ≃ {k : K // p k ≠ none} :=
    Equiv.subtypeEquivRight (fun k => by simp [forcedSet])
  calc
    forcedCount p = Fintype.card (forcedSet p : Set K) :=
      (Fintype.card_congr e).symm
    _ = (forcedSet p).card := Fintype.card_coe _

lemma sum_forcedSet_capacity [Fintype α] [Fintype K] (p : α → K → Option Bool)
    (hsep : ∀ a b, a ≠ b → ∃ k x y, p a k = some x ∧ p b k = some y ∧ x ≠ y) :
    ∑ a, 2 ^ (Fintype.card K - (forcedSet (p a)).card) ≤ 2 ^ Fintype.card K := by
  simpa only [forcedCount_eq_card] using sum_capacity p hsep

lemma forcedCount_eq_card_filter [Fintype K] (p : K → Option Bool) :
    forcedCount p = (Finset.univ.filter (fun k => p k ≠ none)).card := by
  simpa only [forcedSet] using forcedCount_eq_card p

end ChoiceSubcube

namespace AndChoiceKraft
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2583.SingleUse
open PEqualNP.Outside.L_meta_2583.AndSignature
open PEqualNP.Outside.L_meta_2583.AndPairSeparation
open PEqualNP.Outside.L_meta_2583.AndChoiceBridge
open PEqualNP.Outside.L_meta_2583.ChoiceSubcube
open scoped BigOperators

def oppositeAnds (n : ℕ) (C : Circuit) (x : Fin n → Bool) : Finset ℕ :=
  (andPrefix C C.gates.length).filter (fun k =>
    wv n C x (opnd C k 0) ≠ wv n C x (opnd C k 1))

lemma forcedCount_gateChoices (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    forcedCount (gateChoices n C x) = (oppositeAnds n C x).card := by
  classical
  rw [forcedCount_eq_card]
  apply Finset.card_bij (fun k _ => k.val)
  · intro k hk
    have hchoice : choiceAt n C x k.val ≠ none := (Finset.mem_filter.mp hk).2
    exact Finset.mem_filter.mpr ⟨k.property, (choiceAt_forced_iff n C x k.val).mp hchoice⟩
  · intro k hk l hl hkl
    exact Subtype.ext hkl
  · intro k hk
    have hkA := (Finset.mem_filter.mp hk).1
    refine ⟨⟨k, hkA⟩, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,
      (choiceAt_forced_iff n C x k).mpr (Finset.mem_filter.mp hk).2⟩

lemma false_family_capacity {α : Type} [Fintype α]
    (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (f : α → Fin n → Bool)
    (hfalse : ∀ a, C.eval (List.ofFn (f a)) = false)
    (hjoin : ∀ a b, a ≠ b → C.eval (List.ofFn (fun i => f a i || f b i)) = true) :
    ∑ a : α, 2 ^ ((andPrefix C C.gates.length).card - (oppositeAnds n C (f a)).card) ≤
      2 ^ (andPrefix C C.gates.length).card := by
  have h := sum_capacity (fun a => gateChoices n C (f a))
    (family_choices_separate n C hAO f hfalse hjoin)
  simpa only [Fintype.card_coe, forcedCount_gateChoices] using h

end AndChoiceKraft

namespace Q3DirtySeed66
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583
open Q3PackedCertificate

def seedC : Circuit := ⟨[
  { op := GateOp.or, inputs := [14, 17] },
  { op := GateOp.or, inputs := [26, 20] },
  { op := GateOp.or, inputs := [27, 23] },
  { op := GateOp.and, inputs := [0, 28] },
  { op := GateOp.or, inputs := [17, 18] },
  { op := GateOp.or, inputs := [30, 19] },
  { op := GateOp.and, inputs := [1, 31] },
  { op := GateOp.or, inputs := [16, 17] },
  { op := GateOp.or, inputs := [33, 22] },
  { op := GateOp.or, inputs := [34, 24] },
  { op := GateOp.and, inputs := [2, 35] },
  { op := GateOp.or, inputs := [15, 17] },
  { op := GateOp.or, inputs := [37, 21] },
  { op := GateOp.or, inputs := [38, 25] },
  { op := GateOp.and, inputs := [3, 39] },
  { op := GateOp.or, inputs := [14, 19] },
  { op := GateOp.or, inputs := [41, 22] },
  { op := GateOp.or, inputs := [42, 25] },
  { op := GateOp.and, inputs := [5, 43] },
  { op := GateOp.or, inputs := [14, 18] },
  { op := GateOp.or, inputs := [45, 21] },
  { op := GateOp.or, inputs := [46, 24] },
  { op := GateOp.and, inputs := [6, 47] },
  { op := GateOp.or, inputs := [13, 23] },
  { op := GateOp.or, inputs := [49, 24] },
  { op := GateOp.or, inputs := [50, 25] },
  { op := GateOp.and, inputs := [7, 51] },
  { op := GateOp.or, inputs := [16, 19] },
  { op := GateOp.or, inputs := [53, 21] },
  { op := GateOp.or, inputs := [54, 23] },
  { op := GateOp.and, inputs := [8, 55] },
  { op := GateOp.or, inputs := [15, 18] },
  { op := GateOp.or, inputs := [57, 22] },
  { op := GateOp.or, inputs := [58, 23] },
  { op := GateOp.and, inputs := [9, 59] },
  { op := GateOp.or, inputs := [13, 20] },
  { op := GateOp.or, inputs := [61, 21] },
  { op := GateOp.or, inputs := [62, 22] },
  { op := GateOp.and, inputs := [10, 63] },
  { op := GateOp.or, inputs := [15, 19] },
  { op := GateOp.or, inputs := [65, 20] },
  { op := GateOp.or, inputs := [66, 24] },
  { op := GateOp.and, inputs := [11, 67] },
  { op := GateOp.or, inputs := [16, 18] },
  { op := GateOp.or, inputs := [69, 20] },
  { op := GateOp.or, inputs := [70, 25] },
  { op := GateOp.and, inputs := [12, 71] },
  { op := GateOp.or, inputs := [14, 15] },
  { op := GateOp.or, inputs := [73, 16] },
  { op := GateOp.or, inputs := [1, 4] },
  { op := GateOp.or, inputs := [13, 4] },
  { op := GateOp.or, inputs := [13, 74] },
  { op := GateOp.and, inputs := [75, 76] },
  { op := GateOp.and, inputs := [78, 77] },
  { op := GateOp.or, inputs := [29, 32] },
  { op := GateOp.or, inputs := [80, 36] },
  { op := GateOp.or, inputs := [81, 40] },
  { op := GateOp.or, inputs := [82, 44] },
  { op := GateOp.or, inputs := [83, 48] },
  { op := GateOp.or, inputs := [84, 52] },
  { op := GateOp.or, inputs := [85, 56] },
  { op := GateOp.or, inputs := [86, 60] },
  { op := GateOp.or, inputs := [87, 64] },
  { op := GateOp.or, inputs := [88, 68] },
  { op := GateOp.or, inputs := [89, 72] },
  { op := GateOp.or, inputs := [90, 79] }
], 91⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma checks : IsAO2 26 seedC ∧ seedC.size = 66 ∧
    PackedEval.eval seedC pairWords = incidenceMask ∧
    (∀ h : Fin 8, PackedEval.eval seedC (Q3ChunkedCertificate.words h) = 0) := by
  decide +kernel

lemma exact_semantics : ∀ z : Fin 26 → Bool, seedC.eval (List.ofFn z) =
    decide (∃ p l : Fin 13, I p l ∧ z (Fin.castAdd 13 p) = true ∧
      z (Fin.natAdd 13 l) = true) :=
  Q3ChunkedCertificate.exact_of_chunks seedC checks.1 checks.2.2.1 checks.2.2.2

end Q3DirtySeed66

end PEqualNP.Outside.L_meta_2583
