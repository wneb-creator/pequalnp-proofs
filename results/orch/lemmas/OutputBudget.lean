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

namespace PEqualNP.Outside.L_meta_4970.OutputBoundary

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

lemma s2233_gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma s2233_gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [s2233_gateAt_eq hj]; exact List.getElem_mem hj

open PEqualNP.CleanedNonEdge

lemma s2233_orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma s2233_orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [s2233_orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
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
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
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
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
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
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma s2233_orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := s2233_orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
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

lemma s2233_tail_step (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w, OrReaches n C w g → g ≠ w - n →
      ∃ k, k < C.gates.length ∧ OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        n + g ∈ (gateAt C k).inputs := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h hne
    have hnw : n ≤ w := h.1
    obtain ⟨k0, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (s2233_orReaches_iff n C k0 g).mp h
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hr⟩
    · exact (hne (by omega)).elim
    · have hself : OrReaches n C (n + k0) k0 :=
        (s2233_orReaches_iff n C k0 k0).mpr ⟨hk, Or.inl rfl⟩
      by_cases hg : g = i - n
      · refine ⟨k0, hk, hself, hop, ?_⟩
        have hni : n ≤ i := hr.1
        have e : n + g = i := by omega
        rw [e]
        exact hi
      · obtain ⟨k, hkl, hrk, hopk, hin⟩ := ih i hlt hr hg
        exact ⟨k, hkl,
          (s2233_orReaches_iff n C k0 k).mpr ⟨hk, Or.inr ⟨hop, i, hi, hlt, hrk⟩⟩, hopk, hin⟩

def s2233_par (n : ℕ) (C : Circuit) (O : Finset ℕ) : Finset ℕ :=
  O.biUnion (fun k => ((gateAt C k).inputs.toFinset).image (fun w => w - n))

lemma s2233_par_card (n : ℕ) (C : Circuit) (O : Finset ℕ)
    (h : ∀ k ∈ O, (gateAt C k).inputs.length = 2) : (s2233_par n C O).card ≤ O.card * 2 := by
  unfold s2233_par
  calc (O.biUnion (fun k => ((gateAt C k).inputs.toFinset).image (fun w => w - n))).card
      ≤ ∑ k ∈ O, (((gateAt C k).inputs.toFinset).image (fun w => w - n)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ O, 2 := by
        apply Finset.sum_le_sum
        intro k hk
        exact Finset.card_image_le.trans
          ((List.toFinset_card_le _).trans (le_of_eq (h k hk)))
    _ = O.card * 2 := by rw [Finset.sum_const, smul_eq_mul]

lemma output_and_boundary_card_le : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  intro n C F hC hF
  obtain ⟨_, _, hlen⟩ := hC
  obtain ⟨O, hO⟩ : ∃ O : Finset ℕ, ∀ i, i ∈ O ↔ (i < C.gates.length ∧
      (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i) :=
      by
    have hfin : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
        OrReaches n C C.output i}.Finite := by
      apply (Finset.finite_toSet (Finset.range C.gates.length)).subset
      intro i hi
      have hi2 : i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
          OrReaches n C C.output i := Eq.mp Set.mem_setOf_eq hi
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr hi2.1)
    refine ⟨hfin.toFinset, fun i => ?_⟩
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hset : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      OrReaches n C C.output i} = (↑O : Set ℕ) := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.mem_coe, hO]
  rw [hset, Set.ncard_coe_finset]
  have hdisj : Disjoint F O := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have h1 := (hF a ha).2.1
    have h2 := ((hO a).mp hb).2.1
    rw [h1] at h2
    exact GateOp.noConfusion h2
  have hsub : F ∪ O ⊆ insert (C.output - n) (s2233_par n C O) := by
    intro g hg
    have hr : OrReaches n C C.output g := by
      rcases Finset.mem_union.mp hg with h | h
      · exact (hF g h).2.2
      · exact ((hO g).mp h).2.2
    by_cases hgo : g = C.output - n
    · exact Finset.mem_insert.mpr (Or.inl hgo)
    · obtain ⟨k, hk, hrk, hop, hin⟩ := s2233_tail_step n C g C.output hr hgo
      refine Finset.mem_insert.mpr (Or.inr ?_)
      unfold s2233_par
      exact Finset.mem_biUnion.mpr ⟨k, (hO k).mpr ⟨hk, hop, hrk⟩,
        Finset.mem_image.mpr ⟨n + g, List.mem_toFinset.mpr hin, by omega⟩⟩
  have hcard := s2233_par_card n C O (fun k hk => hlen _ (s2233_gateAt_mem ((hO k).mp hk).1))
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at h1
  have h2 := Finset.card_insert_le (C.output - n) (s2233_par n C O)
  omega


end PEqualNP.Outside.L_meta_4970.OutputBoundary

namespace PEqualNP.Outside.L_meta_4970.OutputBoundary

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

def andIndices (C : Circuit) : Finset ℕ :=
  (Finset.range C.size).filter fun j => (gateAt C j).op = GateOp.and

def outputOrIndices (n : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range C.size).filter fun j =>
    (gateAt C j).op = GateOp.or ∧ OrReaches n C C.output j

lemma owned_and_boundary_budget (n : ℕ) (C : Circuit) (K B : Finset ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hreject : ∀ v : Fin n, circuitFun n C (fun i => decide (i = v)) = false)
    (hK : ∀ j ∈ K, j < C.size ∧ (gateAt C j).op = GateOp.or ∧
      ∃ v : Fin n, OrSeparation.sep_W n C (fun i => decide (i = v)) (n + j) = true)
    (hB : ∀ j ∈ B, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j) :
    K.card + (andIndices C).card + B.card ≤ C.size + 1 := by
  classical
  have hbo := output_and_boundary_card_le n C B hAO hB
  have hset : {j : ℕ | j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧
      OrReaches n C C.output j} = (↑(outputOrIndices n C) : Set ℕ) := by
    ext j
    simp [outputOrIndices, Circuit.size, and_assoc]
  rw [hset, Set.ncard_coe_finset] at hbo
  have hKA : Disjoint K (andIndices C) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    have ho := (hK j hj).2.1
    have ha := (Finset.mem_filter.mp hk).2
    rw [ho] at ha
    exact GateOp.noConfusion ha
  have hKO : Disjoint K (outputOrIndices n C) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    exact OrSeparation.singleton_true_excludes_output_or_closure n C hreject j
      (hK j hj).2.2 (Finset.mem_filter.mp hk).2.2
  have hAO' : Disjoint (andIndices C) (outputOrIndices n C) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    have ha := (Finset.mem_filter.mp hj).2
    have ho := (Finset.mem_filter.mp hk).2.1
    rw [ha] at ho
    exact GateOp.noConfusion ho
  have hUO : Disjoint (K ∪ andIndices C) (outputOrIndices n C) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    rcases Finset.mem_union.mp hj with hj | hj
    · exact Finset.disjoint_left.mp hKO hj hk
    · exact Finset.disjoint_left.mp hAO' hj hk
  have hsub : (K ∪ andIndices C) ∪ outputOrIndices n C ⊆ Finset.range C.size := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · rcases Finset.mem_union.mp hj with hj | hj
      · exact Finset.mem_range.mpr (hK j hj).1
      · exact (Finset.mem_filter.mp hj).1
    · exact (Finset.mem_filter.mp hj).1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hUO, Finset.card_union_of_disjoint hKA,
    Finset.card_range] at hc
  omega

end PEqualNP.Outside.L_meta_4970.OutputBoundary
