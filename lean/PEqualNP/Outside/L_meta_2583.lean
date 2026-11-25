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

end PEqualNP.Outside.L_meta_2583
