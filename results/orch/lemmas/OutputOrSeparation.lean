import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970.OrSeparation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def sep_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma sep_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl sep_stepWire x := rfl

lemma sep_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl sep_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [sep_stepWire]
    omega

lemma sep_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl sep_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (sep_stepWire w g).length := by simp [sep_stepWire]; omega
    rw [ih (sep_stepWire w g) hlt]
    simp [sep_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma sep_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma sep_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [sep_wires_eq_foldl, sep_foldl_stepWire_length, List.length_ofFn]

lemma sep_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def sep_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma sep_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma sep_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    sep_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then sep_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := sep_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [sep_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl sep_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, sep_foldl_stepWire_length, hpre_len]
  have hCj : sep_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [sep_W]
    rw [sep_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [sep_foldl_stepWire_getD_lt post (sep_stepWire w0 gj) (n + k) (by simp [sep_stepWire]; omega)]
    simp [sep_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [sep_W]
    rw [sep_wires_eq_foldl, hgs, List.foldl_append]
    exact (sep_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact sep_getD_ge_length w0 i (by omega)

open PEqualNP.CleanedNonEdge in
lemma sep_orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma sep_orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma sep_orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma sep_orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact sep_orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma sep_orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := sep_split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [sep_gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [sep_orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, sep_orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, sep_orFold_getD_lt n post _ m (by omega)]
    exact sep_orStep_getD_lt n _ gk m (by omega)
  have h3 := sep_orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩


lemma sep_W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.or) (i : ℕ) (hi : i ∈ (gateAt C r).inputs)
    (hlt : i < n + r) (hv : sep_W n C x i = true) : sep_W n C x (n + r) = true := by
  rw [sep_W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  exact ⟨i, hi, by rw [ite_eq_left hlt]; exact hv⟩

open PEqualNP.CleanedNonEdge in
lemma sep_reach_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : sep_W n C x (n + g) = true) :
    ∀ k, k < C.gates.length → g ∈ (orSets n C).getD k [] → sep_W n C x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hmem
    rcases (sep_orSets_mem_iff n C k g hk).mp hmem with h | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [← h]; exact hv
    · have h3 := ih (w - n) (by omega) (by omega) hx
      have e : n + (w - n) = w := by omega
      rw [e] at h3
      exact sep_W_or n C x k hk hop w hw hlt h3

open PEqualNP.CleanedNonEdge in
lemma sep_reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w g : ℕ)
    (h : OrReaches n C w g) (hv : sep_W n C x (n + g) = true) : sep_W n C x w = true := by
  obtain ⟨hn, hmem⟩ := h
  by_cases hk : w - n < C.gates.length
  · have h3 := sep_reach_val n C x g hv (w - n) hk hmem
    have e : n + (w - n) = w := by omega
    rw [e] at h3
    exact h3
  · exfalso
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets; rw [sep_orFold_length]; simp
    have hge : (orSets n C).length ≤ w - n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
    simp at hmem

lemma output_rejects_singletons (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hcorrect : ∀ x : Fin (p + l) → Bool,
      circuitFun (p + l) C x = decide (∃ (a : Fin p) (b : Fin l),
        (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    ∀ v : Fin (p + l), circuitFun (p + l) C (fun i => decide (i = v)) = false := by
  intro v
  rw [hcorrect]
  apply decide_eq_false
  rintro ⟨a, b, he, ha, hb⟩
  have hva : Fin.castAdd l a = v := of_decide_eq_true ha
  have hvb : Fin.natAdd p b = v := of_decide_eq_true hb
  have hval := congrArg Fin.val (hva.trans hvb.symm)
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
  have := a.isLt
  omega

lemma singleton_true_excludes_output_or_closure (n : ℕ) (C : Circuit)
    (hreject : ∀ v : Fin n, circuitFun n C (fun i => decide (i = v)) = false)
    (g : ℕ) (hpos : ∃ v : Fin n, sep_W n C (fun i => decide (i = v)) (n + g) = true) :
    ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output g := by
  intro hreach
  obtain ⟨v, hv⟩ := hpos
  have htrue := sep_reach_up n C (fun i => decide (i = v)) C.output g hreach hv
  change circuitFun n C (fun i => decide (i = v)) = true at htrue
  rw [hreject v] at htrue
  exact Bool.false_ne_true htrue

lemma large_support_excludes_output_or_closure (n : ℕ) (C : Circuit)
    (hreject : ∀ v : Fin n, circuitFun n C (fun i => decide (i = v)) = false)
    (g : ℕ)
    (hlarge : 2 ≤ (Finset.univ.filter fun v : Fin n =>
      sep_W n C (fun i => decide (i = v)) (n + g) = true).card) :
    ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output g := by
  apply singleton_true_excludes_output_or_closure n C hreject g
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter fun v : Fin n =>
    sep_W n C (fun i => decide (i = v)) (n + g) = true).card)
  exact ⟨v, (Finset.mem_filter.mp hv).2⟩

lemma positive_supports_disjoint_output_closure (n : ℕ) (C : Circuit) (K : Finset ℕ)
    (hreject : ∀ v : Fin n, circuitFun n C (fun i => decide (i = v)) = false)
    (hpos : ∀ w ∈ K, n ≤ w ∧ ∃ v : Fin n,
      sep_W n C (fun i => decide (i = v)) w = true) :
    Disjoint K ((Finset.Ico n (n + C.size)).filter fun w =>
      PEqualNP.CleanedNonEdge.OrReaches n C C.output (w - n)) := by
  apply Finset.disjoint_left.mpr
  intro w hw hreach
  obtain ⟨hn, v, hv⟩ := hpos w hw
  apply singleton_true_excludes_output_or_closure n C hreject (w - n) ?_
    (Finset.mem_filter.mp hreach).2
  refine ⟨v, ?_⟩
  simpa only [Nat.add_sub_of_le hn] using hv

end PEqualNP.Outside.L_meta_4970.OrSeparation
