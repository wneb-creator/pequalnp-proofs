import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970.MultiBudget

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

lemma support_and {n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    {k : ℕ} (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and) (u : Fin n) :
    u ∈ singletonSupport n C (n+k) ↔
      ∀ w ∈ (gateAt C k).inputs, u ∈ singletonSupport n C w := by
  simp only [mem_support, val_and (by simp : (List.ofFn (pairInput u u)).length = n) hk hop]
  exact ⟨fun h w hw => (h w hw).2,fun h w hw => ⟨rb k hk w hw,h w hw⟩⟩

def positiveInputs (n : ℕ) (C : Circuit) (k : ℕ) : Finset ℕ := by
  classical
  exact (gateAt C k).inputs.toFinset.filter fun w => (singletonSupport n C w).Nonempty

lemma mem_positiveInputs {n : ℕ} {C : Circuit} {k w : ℕ} :
    w ∈ positiveInputs n C k ↔ w ∈ (gateAt C k).inputs ∧ (singletonSupport n C w).Nonempty := by
  classical
  simp [positiveInputs]

noncomputable def births (n : ℕ) (C : Circuit) (R : Finset ℕ) : Finset ℕ := by
  classical
  exact R.filter fun k => (gateAt C k).op = GateOp.and ∧
    singletonSupport n C (n+k) = ∅ ∧
    ∃ a b, (gateAt C k).inputs = [a,b] ∧
      (singletonSupport n C a).Nonempty ∧ (singletonSupport n C b).Nonempty

noncomputable def merges (n : ℕ) (C : Circuit) (R : Finset ℕ) : Finset ℕ := by
  classical
  exact R.filter fun k => (gateAt C k).op = GateOp.or ∧
    1 < (singletonSupport n C (n+k)).card ∧ 1 < (positiveInputs n C k).card

noncomputable def andExtras (n : ℕ) (C : Circuit) (R : Finset ℕ) : Finset ℕ := by
  classical
  exact R.filter fun k => (gateAt C k).op = GateOp.and ∧ k ∉ births n C R ∧
    ((singletonSupport n C (n+k)).Nonempty ∨ (positiveInputs n C k).Nonempty)

lemma gate_budget_with_extras {n : ℕ} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (R : Finset ℕ) (hR : ∀ k ∈ R, k < C.gates.length)
    (hread : ∀ j ∈ R, singletonSupport n C (n+j) = ∅ → j ≠ C.output-n →
      ∃ k ∈ R, n+j ∈ (gateAt C k).inputs) :
    2 * (births n C R).card + (merges n C R).card +
      (andExtras n C R).card ≤ R.card + 1 := by
  classical
  let Z := R.filter fun k => singletonSupport n C (n+k) = ∅
  let D := fun k => (gateAt C k).inputs.toFinset.filter fun w =>
    n ≤ w ∧ singletonSupport n C w = ∅
  let E := fun k => (D k).image fun w => w-n
  have hZ (k) : k ∈ Z ↔ k ∈ R ∧ singletonSupport n C (n+k) = ∅ := Finset.mem_filter
  have hread' : Z.erase (C.output-n) ⊆ R.biUnion E := by
    intro j hj
    obtain ⟨hne,hz⟩ := Finset.mem_erase.mp hj
    obtain ⟨k,hk,hin⟩ := hread j ((hZ j).mp hz).1 ((hZ j).mp hz).2 hne
    refine Finset.mem_biUnion.mpr ⟨k,hk,Finset.mem_image.mpr ⟨n+j,?_,by omega⟩⟩
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hin,by omega,((hZ j).mp hz).2⟩
  have hsum : Z.card ≤ (∑ k ∈ R, (D k).card) + 1 := by
    calc
      Z.card ≤ (Z.erase (C.output-n)).card + 1 := by
        by_cases h : C.output-n ∈ Z
        · exact Nat.le_of_eq (Finset.card_erase_add_one h).symm
        · rw [Finset.erase_eq_of_notMem h]; omega
      _ ≤ (R.biUnion E).card + 1 := Nat.add_le_add_right (Finset.card_le_card hread') _
      _ ≤ (∑ k ∈ R, (E k).card) + 1 := Nat.add_le_add_right Finset.card_biUnion_le _
      _ ≤ _ := Nat.add_le_add_right (Finset.sum_le_sum fun _ _ => Finset.card_image_le) _
  have hlocal : ∀ k ∈ R, (D k).card + 2 * (if k ∈ births n C R then 1 else 0) +
      (if k ∈ merges n C R then 1 else 0) +
      (if k ∈ andExtras n C R then 1 else 0) ≤ 1 + (if k ∈ Z then 1 else 0) := by
    intro k hk
    have hdp : Disjoint (D k) (positiveInputs n C k) := by
      rw [Finset.disjoint_left]
      intro w hd hp
      have he := (Finset.mem_filter.mp hd).2.2
      simpa [he] using (mem_positiveInputs.mp hp).2
    have hcap : (D k).card + (positiveInputs n C k).card ≤ 2 := by
      rw [← Finset.card_union_of_disjoint hdp]
      exact (Finset.card_le_card (Finset.union_subset
        (Finset.filter_subset _ _) (Finset.filter_subset _ _))).trans (input_card hm (hR k hk))
    by_cases hb : k ∈ births n C R
    · obtain ⟨_,hop,hempty,a,b,hab,ha,hb'⟩ := Finset.mem_filter.mp hb
      have hz := (hZ k).mpr ⟨hk,hempty⟩
      have hl : k ∉ merges n C R := by
        intro h
        have hh := (Finset.mem_filter.mp h).2.1
        rw [hop] at hh
        cases hh
      have hd : D k = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        have hw' := Finset.mem_filter.mp hw
        have hh : w=a ∨ w=b := by simpa [hab] using hw'.1
        rcases hh with rfl | rfl
        · simp [hw'.2.2] at ha
        · simp [hw'.2.2] at hb'
      have hj : k ∉ andExtras n C R := by
        intro h
        exact (Finset.mem_filter.mp h).2.2.1 hb
      simp [hb,hz,hl,hd,hj]
    · by_cases hl : k ∈ merges n C R
      · have hpos := (Finset.mem_filter.mp hl).2.2.2
        have hj : k ∉ andExtras n C R := by
          intro h
          have hop := (Finset.mem_filter.mp h).2.1
          have hor := (Finset.mem_filter.mp hl).2.1
          rw [hop] at hor
          cases hor
        simp only [hb,hl,hj,ite_false,ite_true,Nat.mul_zero,Nat.add_zero]
        split_ifs <;> omega
      · by_cases hj : k ∈ andExtras n C R
        · obtain ⟨_,hop,_,hpos⟩ := Finset.mem_filter.mp hj
          by_cases hz : k ∈ Z
          · have hp : (positiveInputs n C k).Nonempty := by
              rcases hpos with hpos | hpos
              · have hempty := ((hZ k).mp hz).2
                simpa [hempty] using hpos
              · exact hpos
            have hpc := Finset.card_pos.mpr hp
            simp only [hb,hl,hj,hz,ite_false,ite_true,Nat.mul_zero,Nat.add_zero]
            omega
          · have hs : (singletonSupport n C (n+k)).Nonempty :=
              Finset.nonempty_iff_ne_empty.mpr fun h => hz ((hZ k).mpr ⟨hk,h⟩)
            obtain ⟨u,hu⟩ := hs
            have hd : D k=∅ := by
              apply Finset.eq_empty_iff_forall_notMem.mpr
              intro w hw
              obtain ⟨hwi,_,hwzero⟩ := Finset.mem_filter.mp hw
              have hu' := (support_and rb (hR k hk) hop u).mp hu w (List.mem_toFinset.mp hwi)
              simpa [hwzero] using hu'
            simp [hb,hl,hj,hz,hd]
        · by_cases hz : k ∈ Z
          · simp only [hb,hl,hj,hz,ite_false,ite_true,Nat.mul_zero,Nat.add_zero]
            omega
          · have hs : (singletonSupport n C (n+k)).Nonempty :=
              Finset.nonempty_iff_ne_empty.mpr fun h => hz ((hZ k).mpr ⟨hk,h⟩)
            obtain ⟨u,hu⟩ := hs
            have hdle : (D k).card ≤ 1 := by
              rcases gate_op hm (hR k hk) with hop | hop
              · have hd : D k=∅ := by
                  apply Finset.eq_empty_iff_forall_notMem.mpr
                  intro w hw
                  obtain ⟨hwi,_,hwzero⟩ := Finset.mem_filter.mp hw
                  have hu' := (support_and rb (hR k hk) hop u).mp hu w (List.mem_toFinset.mp hwi)
                  simpa [hwzero] using hu'
                simp [hd]
              · obtain ⟨w,hw,huw⟩ := (support_or rb (hR k hk) hop u).mp hu
                have hpos := Finset.card_pos.mpr ⟨w,mem_positiveInputs.mpr ⟨hw,u,huw⟩⟩
                omega
            simp only [hb,hl,hj,hz,ite_false,Nat.mul_zero,Nat.add_zero]
            omega
  have count (T : Finset ℕ) (hT : T ⊆ R) :
      (∑ k ∈ R, if k ∈ T then 1 else 0) = T.card := by
    rw [← Finset.card_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter]
    exact ⟨And.right,fun h => ⟨hT h,h⟩⟩
  have h := Finset.sum_le_sum hlocal
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    count (births n C R) (Finset.filter_subset _ _),count (merges n C R) (Finset.filter_subset _ _),
    count (andExtras n C R) (Finset.filter_subset _ _),
    Finset.sum_add_distrib,count Z (Finset.filter_subset _ _)] at h
  simp only [Finset.sum_const,smul_eq_mul,mul_one] at h
  omega

lemma gate_budget {n : ℕ} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (R : Finset ℕ) (hR : ∀ k ∈ R, k < C.gates.length)
    (hread : ∀ j ∈ R, singletonSupport n C (n+j) = ∅ → j ≠ C.output-n →
      ∃ k ∈ R, n+j ∈ (gateAt C k).inputs) :
    2 * (births n C R).card + (merges n C R).card ≤ R.card + 1 := by
  have h := gate_budget_with_extras hm rb R hR hread
  omega

noncomputable def selectedCone (n : ℕ) (C : Circuit) (T : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun k => ∃ o ∈ T, reachable n ⟨C.gates,o⟩ k

lemma selected_terminal_budget_with_extras {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    (rb : ReadsBack n C) (T : Finset ℕ)
    (hT : ∀ o ∈ T, o ≠ C.output → (singletonSupport n C o).Nonempty) :
    2 * (births n C (selectedCone n C T)).card +
      (merges n C (selectedCone n C T)).card +
      (andExtras n C (selectedCone n C T)).card ≤ C.size+1 := by
  classical
  let R := selectedCone n C T
  have hR : ∀ k ∈ R, k<C.gates.length := fun k hk =>
    Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  have hread : ∀ j ∈ R, singletonSupport n C (n+j)=∅ → j≠C.output-n →
      ∃ k ∈ R, n+j ∈ (gateAt C k).inputs := by
    intro j hj hz hne
    obtain ⟨o,ho,hjo⟩ := (Finset.mem_filter.mp hj).2
    have hno : j≠o-n := by
      intro he
      have hwire : n+j=o := by
        rcases hjo.2 with hjo | hjo
        · exact hjo
        · obtain ⟨_,k,hk,_,_⟩ := (inCone_iff n ⟨C.gates,o⟩ j (o-n)).mp hjo
          omega
      have ho' : o≠C.output := by intro he'; apply hne; omega
      have hp := hT o ho ho'
      rw [← hwire,hz] at hp
      exact Finset.not_nonempty_empty hp
    obtain ⟨k,hk,hinput⟩ := reachable_reader hjo hno
    refine ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk.1,⟨o,ho,hk⟩⟩,hinput⟩
  have h := gate_budget_with_extras hm rb R hR hread
  have hc : R.card ≤ C.size := by
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  exact h.trans (Nat.add_le_add_right hc 1)


lemma pure_or_multioutput_budget_with_extras {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (W : Finset ℕ)
    (hW : ∀ w ∈ W, ∃ Q : Finset (Fin n), Q.Nonempty ∧
      ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false =
        decide (∃ u ∈ Q,x u=true)) :
    2 * (births n C (selectedCone n C (insert C.output W))).card +
      (merges n C (selectedCone n C (insert C.output W))).card +
      (andExtras n C (selectedCone n C (insert C.output W))).card ≤ C.size+1 := by
  classical
  have hm : Monotone2 C := fun g hg => ⟨hAO.1 g hg,(hAO.2.2 g hg).le⟩
  apply selected_terminal_budget_with_extras hm hAO.2.1
  intro o ho hne
  have hoW : o ∈ W := (Finset.mem_insert.mp ho).resolve_left hne
  obtain ⟨Q,hQ,hfun⟩ := hW o hoW
  obtain ⟨u,hu⟩ := hQ
  refine ⟨u,?_⟩
  rw [mem_support]
  change (C.wires (List.ofFn (pairInput u u))).getD o false = true
  rw [hfun]
  exact decide_eq_true ⟨u,hu,by simp [pairInput]⟩


lemma selected_terminal_budget {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    (rb : ReadsBack n C) (T : Finset ℕ)
    (hT : ∀ o ∈ T, o ≠ C.output → (singletonSupport n C o).Nonempty) :
    2 * (births n C (selectedCone n C T)).card +
      (merges n C (selectedCone n C T)).card ≤ C.size+1 := by
  have h := selected_terminal_budget_with_extras hm rb T hT
  omega

lemma pure_or_multioutput_budget {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (W : Finset ℕ)
    (hW : ∀ w ∈ W, ∃ Q : Finset (Fin n), Q.Nonempty ∧
      ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false =
        decide (∃ u ∈ Q,x u=true)) :
    2 * (births n C (selectedCone n C (insert C.output W))).card +
      (merges n C (selectedCone n C (insert C.output W))).card ≤ C.size+1 := by
  have h := pure_or_multioutput_budget_with_extras hAO W hW
  omega

end PEqualNP.Outside.L_meta_4970.MultiBudget
