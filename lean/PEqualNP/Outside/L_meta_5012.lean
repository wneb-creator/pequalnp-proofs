import Mathlib.Order.Preorder.Finite
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012

namespace Semantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
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
lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have h3 := orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩


lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.or) (i : ℕ) (hi : i ∈ (gateAt C r).inputs)
    (hlt : i < n + r) (hv : W n C x i = true) : W n C x (n + r) = true := by
  rw [W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  exact ⟨i, hi, by rw [if_pos hlt]; exact hv⟩

open PEqualNP.CleanedNonEdge in
lemma reach_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : W n C x (n + g) = true) :
    ∀ k, k < C.gates.length → g ∈ (orSets n C).getD k [] → W n C x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hmem
    rcases (orSets_mem_iff n C k g hk).mp hmem with h | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [← h]; exact hv
    · have h3 := ih (w - n) (by omega) (by omega) hx
      have e : n + (w - n) = w := by omega
      rw [e] at h3
      exact W_or n C x k hk hop w hw hlt h3

open PEqualNP.CleanedNonEdge in
lemma reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w g : ℕ)
    (h : OrReaches n C w g) (hv : W n C x (n + g) = true) : W n C x w = true := by
  obtain ⟨hn, hmem⟩ := h
  by_cases hk : w - n < C.gates.length
  · have h3 := reach_val n C x g hv (w - n) hk hmem
    have e : n + (w - n) = w := by omega
    rw [e] at h3
    exact h3
  · exfalso
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets; rw [orFold_length]; simp
    have hge : (orSets n C).length ≤ w - n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
    simp at hmem

lemma mem_filter_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α)
    (h : a ∈ @Finset.filter α p d s) : p a :=
  ((@Finset.mem_filter α p d s a).mp h).2

lemma side_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (b : Fin 2) (i : Fin n)
    (hi : i ∈ PEqualNP.TopForm.side (n := n) C j b) (hx : x i = true) :
    W n C x (PEqualNP.TopForm.opnd C j b) = true := by
  unfold PEqualNP.TopForm.side PEqualNP.TopForm.orIn at hi
  have hi2 := mem_filter_gen _ _ _ _ hi
  rcases hi2 with h | ⟨k, hk, hreach, hop, hin⟩
  · rw [← h, W_input n C x i.val i.isLt]; exact hx
  · have hk1 : W n C x (n + k) = true := by
      apply W_or n C x k hk hop i.val hin (by have := i.isLt; omega)
      rw [W_input n C x i.val i.isLt]; exact hx
    exact reach_up n C x _ k hreach hk1

open PEqualNP.EdgeOwnership in
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
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

open PEqualNP.EdgeOwnership in
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


lemma gateAt_mem' (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq C j hj]; exact List.getElem_mem hj

open PEqualNP.EdgeOwnership in
lemma inCone_lt (n : ℕ) (C : Circuit) : ∀ j i, InCone n C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i h
    obtain ⟨_, k, hk, _, h3⟩ := (inCone_iff n C i j).mp h
    rcases h3 with h3 | h3
    · omega
    · have := ih k hk i h3; omega

open PEqualNP.CleanedNonEdge in
lemma orReach_trans (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (w : ℕ) (hw : w ∈ (gateAt C k).inputs)
    (hlt : w < n + k) (g : ℕ) (h : OrReaches n C w g) : OrReaches n C (n + k) g := by
  obtain ⟨hn, hmem⟩ := h
  refine ⟨by omega, ?_⟩
  have e : n + k - n = k := by omega
  rw [e]
  exact (orSets_mem_iff n C k g hk).mpr (Or.inr ⟨hop, w, hw, hn, hlt, hmem⟩)

open PEqualNP.CleanedNonEdge in
lemma orReach_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := by
  refine ⟨by omega, ?_⟩
  have e : n + k - n = k := by omega
  rw [e]
  exact (orSets_mem_iff n C k k hk).mpr (Or.inl rfl)

lemma orIn_mem (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

open PEqualNP.CleanedNonEdge in
lemma down (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hAO : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ w, W n C x w = true → (∃ i : Fin n, i ∈ PEqualNP.TopForm.orIn n C w ∧ x i = true) ∨
      ∃ k, k < C.gates.length ∧ OrReaches n C w k ∧ (gateAt C k).op = GateOp.and ∧
        W n C x (n + k) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hwn : w < n
    · left
      refine ⟨⟨w, hwn⟩, (orIn_mem n C w _).mpr (Or.inl rfl), ?_⟩
      rw [← W_input n C x w hwn]; exact hv
    · by_cases hk : w - n < C.gates.length
      · have hw : w = n + (w - n) := by omega
        set k := w - n with hkdef
        rcases hAO k hk with hop | hop
        · right
          refine ⟨k, hk, ?_, hop, ?_⟩
          · rw [hw]; exact orReach_self n C k hk
          · rw [← hw]; exact hv
        · have hv2 := hv
          rw [hw, W_gate n C x k hk, hop] at hv2
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv2
          obtain ⟨i, hi, hiv⟩ := hv2
          split_ifs at hiv with hlt
          rcases ih i (by omega) hiv with ⟨j, hj, hxj⟩ | ⟨k', hk', hr, hop', hv'⟩
          · left
            refine ⟨j, ?_, hxj⟩
            rw [orIn_mem] at hj ⊢
            right
            rcases hj with hj | ⟨k'', hk'', hr, hop'', hin⟩
            · refine ⟨k, hk, ?_, hop, ?_⟩
              · rw [hw]; exact orReach_self n C k hk
              · rw [hj]; exact hi
            · refine ⟨k'', hk'', ?_, hop'', hin⟩
              rw [hw]; exact orReach_trans n C k hk hop i hi hlt k'' hr
          · right
            refine ⟨k', hk', ?_, hop', hv'⟩
            rw [hw]; exact orReach_trans n C k hk hop i hi hlt k' hr
      · exfalso
        have hl := wires_length n C x
        have : W n C x w = false := getD_ge_length _ w (by omega)
        rw [this] at hv; exact Bool.false_ne_true hv

open PEqualNP.EdgeOwnership in
lemma orSets_cone (n : ℕ) (C : Circuit) : ∀ m, m < C.gates.length → ∀ k,
    k ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD m [] → k = m ∨ InCone n C k m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm k hk
    rcases (orSets_mem_iff n C m k hm).mp hk with h | ⟨_, w, hw, hn, hlt, hx⟩
    · exact Or.inl h
    · right
      have h2 := ih (w - n) (by omega) (by omega) k hx
      have e : n + (w - n) = w := by omega
      exact (inCone_iff n C k m).mpr ⟨hm, w - n, by omega, by rw [e]; exact hw, h2⟩

open PEqualNP.EdgeOwnership in
lemma reach_cone (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (o : ℕ)
    (ho : o ∈ (gateAt C j).inputs) (hlt : o < n + j) (k : ℕ)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C o k) : InCone n C k j := by
  obtain ⟨hn, hmem⟩ := h
  have h2 := orSets_cone n C (o - n) (by omega) k hmem
  have e : n + (o - n) = o := by omega
  exact (inCone_iff n C k j).mpr ⟨hj, o - n, by omega, by rw [e]; exact ho, h2⟩

lemma firstTwoJunkSemantics : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ), PEqualNP.TopForm.IsAO2 x1 x4 → PEqualNP.TopForm.TopForm x2 x4 → x5 ∈ PEqualNP.TopForm.junk x2 x4 → x6 ∈ PEqualNP.TopForm.junk x2 x4 → x5 < x6 → (∀ x12 ∈ PEqualNP.TopForm.junk x2 x4, x12 < x6 → x12 = x5) → ∀ x13 ∈ [x5, x6], ∀ (x15 : Fin x1 → Bool), PEqualNP.ReadTwo.wval x4 x15 (x1 + x13) = Bool.true ↔ ∀ (x16 : Fin (2 : ℕ)), (∃ x17 ∈ PEqualNP.TopForm.side x4 x13 x16, x15 x17 = Bool.true) ∨ x13 = x6 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x13 x16) x5 ∧ PEqualNP.ReadTwo.wval x4 x15 (x1 + x5) = Bool.true := by
  intro n G _ C x5 x6 hAO hTF h5 h6 h56 hmin x13 hx13 x
  have hWeq : ∀ u, PEqualNP.ReadTwo.wval C x u = W n C x u := fun u => rfl
  simp only [hWeq]
  have hjunk : ∀ j, j ∈ PEqualNP.TopForm.junk G C ↔ j < C.gates.length ∧
      PEqualNP.CleanedNonEdge.IsDirtyAnd n G C j := by
    intro j
    unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
    rw [Finset.mem_filter, Finset.mem_range]
  have hx13' : x13 = x5 ∨ x13 = x6 := by simpa using hx13
  have hj13 : x13 ∈ PEqualNP.TopForm.junk G C := by
    rcases hx13' with h | h <;> rw [h] <;> assumption
  have hle : x13 ≤ x6 := by rcases hx13' with h | h <;> omega
  obtain ⟨hlen13, hop13, _⟩ := (hjunk x13).mp hj13
  obtain ⟨hAOo, hRB, hAO2⟩ := hAO
  have hops : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or :=
    fun k hk => hAOo _ (gateAt_mem' C k hk)
  have hlen2 : (gateAt C x13).inputs.length = 2 := hAO2 _ (gateAt_mem' C x13 hlen13)
  have hopnd_mem : ∀ b : Fin 2, PEqualNP.TopForm.opnd C x13 b ∈ (gateAt C x13).inputs := by
    intro b
    unfold PEqualNP.TopForm.opnd
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  have hin_opnd : ∀ i ∈ (gateAt C x13).inputs, ∃ b : Fin 2, i = PEqualNP.TopForm.opnd C x13 b := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hi
    refine ⟨⟨p, by omega⟩, ?_⟩
    unfold PEqualNP.TopForm.opnd
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
    rfl
  constructor
  · intro hv b
    have hv2 := hv
    rw [W_gate n C x x13 hlen13, hop13] at hv2
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hv2
    have hob := hv2 _ (hopnd_mem b)
    have hlt := hRB x13 hlen13 _ (hopnd_mem b)
    rw [if_pos hlt] at hob
    rcases down n C x hops _ hob with ⟨i, hi, hxi⟩ | ⟨k, hk, hr, hopk, hvk⟩
    · exact Or.inl ⟨i, hi, hxi⟩
    · right
      have hcone := reach_cone n C x13 hlen13 _ (hopnd_mem b) hlt k hr
      have hnb : ¬ PEqualNP.TopForm.BelowF G C k := fun hb => hTF k hk x13 hlen13 hopk hb hop13 hcone
      have hex : ∃ y : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C k y = true ∧
          PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y = false := by
        by_contra hc
        apply hnb
        intro y hy
        by_contra hf
        exact hc ⟨y, hy, Bool.eq_false_iff.mpr hf⟩
      have hkj : k ∈ PEqualNP.TopForm.junk G C := by
        rw [hjunk]
        obtain ⟨y, hy1, hy2⟩ := hex
        exact ⟨hk, hopk, hk, y, hy1, hy2⟩
      have hklt := inCone_lt n C x13 k hcone
      have hk5 := hmin k hkj (by omega)
      subst hk5
      rcases hx13' with h | h
      · omega
      · exact ⟨h, hr, hvk⟩
  · intro h
    rw [W_gate n C x x13 hlen13, hop13]
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro i hi
    rw [if_pos (hRB x13 hlen13 i hi)]
    obtain ⟨b, rfl⟩ := hin_opnd i hi
    rcases h b with ⟨j, hj, hxj⟩ | ⟨_, hr, hv5⟩
    · exact side_val n C x x13 b j hj hxj
    · exact reach_up n C x _ x5 hr hv5

end Semantics

namespace Boundary

lemma monotone_eq_of_extreme_values {α : Type*} [Preorder α] [Finite α]
    (f g : α → Bool) (hf : Monotone f)
    (hmin : ∀ x, Minimal (fun y => g y = true) x → f x = true)
    (hmax : ∀ x, Maximal (fun y => g y = false) x → f x = false) :
    f = g := by
  funext x
  cases hx : g x with
  | false =>
    obtain ⟨y, hxy, hy⟩ :=
      (Set.toFinite {y | g y = false}).exists_le_maximal hx
    have h := hf hxy
    rw [hmax y hy] at h
    cases hfx : f x <;> simp_all
    exact (by decide : ¬ (true : Bool) ≤ false) h
  | true =>
    obtain ⟨y, hyx, hy⟩ :=
      Set.Finite.exists_le_maximal (α := αᵒᵈ)
        (s := {y | g y = true}) (Set.toFinite _) hx
    have h := hf hyx
    rw [hmin y hy] at h
    cases hfx : f x <;> simp_all
    exact (by decide : ¬ (true : Bool) ≤ false) h

lemma bad_value_iff_maximal {α : Type*} [Preorder α] [Finite α]
    (f g : α → Bool) (hf : Monotone f) :
    (∃ x, f x = true ∧ g x = false) ↔
      ∃ x, Maximal (fun y => g y = false) x ∧ f x = true := by
  constructor
  · rintro ⟨x, hfx, hgx⟩
    obtain ⟨y, hxy, hy⟩ :=
      (Set.toFinite {y | g y = false}).exists_le_maximal hgx
    refine ⟨y, hy, ?_⟩
    have h := hf hxy
    rw [hfx] at h
    cases hfy : f y <;> simp_all
    exact (by decide : ¬ (true : Bool) ≤ false) h
  · rintro ⟨x, hx, hfx⟩
    exact ⟨x, hfx, hx.1⟩

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma graphFun_eq_of_boundary {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (f : (Fin n → Bool) → Bool) (hf : Monotone f)
    (hpos : ∀ u v, G.Adj u v → f (pairInput u v) = true)
    (hneg : ∀ x, Maximal (fun y => graphFun G ∅ y = false) x → f x = false) :
    f = graphFun G ∅ := by
  apply monotone_eq_of_extreme_values f (graphFun G ∅) hf
  · intro x hx
    have hxtrue := hx.1
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq] at hxtrue
    obtain ⟨u, v, huv, hu, hv⟩ := hxtrue
    have hpair : pairInput u v ≤ x := by
      intro w
      cases hw : pairInput u v w with
      | false => simp
      | true =>
        have hwuv : w = u ∨ w = v := by simpa [pairInput] using hw
        rcases hwuv with rfl | rfl
        · simp [hu]
        · simp [hv]
    have h := hf hpair
    rw [hpos u v huv] at h
    cases hfx : f x <;> simp_all
    exact (by decide : ¬ (true : Bool) ≤ false) h
  · exact hneg

end Boundary

namespace Color

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.Semantics

lemma orIn_val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (i : Fin n)
    (hi : i ∈ orIn n C w) (hx : x i = true) : W n C x w = true := by
  rcases (orIn_mem n C w i).mp hi with h | ⟨k, hk, hreach, hop, hin⟩
  · rw [← h, W_input n C x i.val i.isLt]
    exact hx
  · apply reach_up n C x w k hreach
    apply W_or n C x k hk hop i.val hin (by have := i.isLt; omega)
    rw [W_input n C x i.val i.isLt]
    exact hx

lemma graphFun_pair_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (h : graphFun G ∅ (pairInput u v) = true) : G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] at h
  obtain ⟨a, b, hab, ha, hb⟩ := h
  have ha' : a = u ∨ a = v := by simpa [pairInput] using ha
  have hb' : b = u ∨ b = v := by simpa [pairInput] using hb
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · exact (G.irrefl hab).elim
  · exact hab
  · exact hab.symm
  · exact (G.irrefl hab).elim

lemma and_true_of_operands {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (x : Fin n → Bool) (h0 : W n C x (opnd C a 0) = true)
    (h1 : W n C x (opnd C a 1) = true) : W n C x (n + a) = true := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem' C a ha))
  have hp : p < n + a := hAO.2.1 a ha p (by rw [hin]; simp)
  have hq : q < n + a := hAO.2.1 a ha q (by rw [hin]; simp)
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  rw [e0] at h0
  rw [e1] at h1
  rw [W_gate n C x a ha, hop, hin]
  simp [GateOp.eval, hp, hq, h0, h1]

lemma lam_has_common_neighbor {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (k : ℕ) (hk : k ∈ lam G C) :
    ∃ c : Fin n, ∀ u ∈ orIn n C (n + k), G.Adj u c := by
  classical
  obtain ⟨_, _, _, a, ha, b, hc, hr⟩ := Finset.mem_filter.mp hk
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hc
  refine ⟨c, ?_⟩
  intro u hu
  have huval : W n C (pairInput u c) (n + k) = true :=
    orIn_val C _ _ u hu (by simp [pairInput])
  have hbval : W n C (pairInput u c) (opnd C a b) = true :=
    reach_up n C _ _ k hr huval
  have hcside : c ∈ side (n := n) C a (1 - b) := by rw [hc]; simp
  have hcval : W n C (pairInput u c) (opnd C a (1 - b)) = true :=
    side_val n C _ a (1 - b) c hcside (by simp [pairInput])
  have htop := ha
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at htop
  obtain ⟨haN', hop, hbelow⟩ := htop
  apply graphFun_pair_adj G u c
  apply hbelow
  change W n C (pairInput u c) (n + a) = true
  have hb : b = 0 ∨ b = 1 := by omega
  rcases hb with rfl | rfl
  · exact and_true_of_operands C hAO a haN' hop _ hbval hcval
  · exact and_true_of_operands C hAO a haN' hop _ hcval hbval

lemma lam_monochromatic {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (s : Fin n → Bool)
    (hs : ∀ u v, G.Adj u v → s u ≠ s v) (k : ℕ) (hk : k ∈ lam G C) :
    ∀ u ∈ orIn n C (n + k), ∀ v ∈ orIn n C (n + k), s u = s v := by
  obtain ⟨c, hc⟩ := lam_has_common_neighbor G C hAO k hk
  intro u hu v hv
  have huc := hs u c (hc u hu)
  have hvc := hs v c (hc v hv)
  cases hsu : s u <;> cases hsv : s v <;> cases hsc : s c <;> simp_all

lemma tight_earlier_or_monochromatic {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (s : Fin n → Bool)
    (hs : ∀ u v, G.Adj u v → s u ≠ s v) (m : ℕ)
    (htight : orN G C \ lam G C = {m}) (k : ℕ) (hkm : k < m)
    (hk : k ∈ orN G C) :
    ∀ u ∈ orIn n C (n + k), ∀ v ∈ orIn n C (n + k), s u = s v := by
  apply lam_monochromatic G C hAO s hs k
  by_contra hn
  have hm : k ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr ⟨hk, hn⟩
  rw [htight, Finset.mem_singleton] at hm
  omega

end Color

namespace SharedOrAccounting

open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

lemma commonCenter_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (S : Finset (Fin n)) (hS : 2 ≤ S.card)
    {c d : Fin n} (hc : ∀ u ∈ S, G.Adj c u) (hd : ∀ u ∈ S, G.Adj d u) : c = d := by
  by_contra hcd
  have hsub : S ⊆ Finset.univ.filter (fun u => G.Adj c u ∧ G.Adj d u) := by
    intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hc u hu, hd u hu⟩
  have := (Finset.card_le_card hsub).trans (h4 c d hcd)
  omega

lemma sharedOr_center_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ)
    (hS : 2 ≤ (orIn n C w).card) {c d : Fin n}
    (hc : ∀ u ∈ orIn n C w, G.Adj c u)
    (hd : ∀ u ∈ orIn n C w, G.Adj d u) : c = d :=
  commonCenter_unique G h4 (orIn n C w) hS hc hd

lemma exists_nonadjacent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (S : Finset (Fin n)) (hS : 2 ≤ S.card)
    {c w : Fin n} (hc : ∀ u ∈ S, G.Adj c u) (hw : w ≠ c) :
    ∃ u ∈ S, ¬ G.Adj w u := by
  classical
  by_contra! hall
  exact hw (commonCenter_unique G h4 S hS hall hc)

lemma neighbors_nonadjacent {n : ℕ} (G : SimpleGraph (Fin n)) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    {c u v : Fin n} (hcu : G.Adj c u) (hcv : G.Adj c v) : ¬ G.Adj u v := by
  intro huv
  have h1 := hbip c u hcu
  have h2 := hbip c v hcv
  have h3 := hbip u v huv
  cases hc : s c <;> cases hu : s u <;> cases hv : s v <;> simp_all

lemma productCleaner_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (A B : Finset (Fin n)) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    {c w : Fin n} (hcA : ∀ u ∈ A, G.Adj c u) (hcB : ∀ v ∈ B, G.Adj c v)
    (hclean : ∀ x : Fin n → Bool,
      (∃ u ∈ A, x u = true) → (∃ v ∈ B, x v = true) → x w = true →
      graphFun G ∅ x = true) : w = c := by
  classical
  by_contra hw
  obtain ⟨u, hu, hwu⟩ := exists_nonadjacent G h4 A hA hcA hw
  obtain ⟨v, hv, hwv⟩ := exists_nonadjacent G h4 B hB hcB hw
  have huv : ¬ G.Adj u v := neighbors_nonadjacent G s hbip (hcA u hu) (hcB v hv)
  let x : Fin n → Bool := fun t => decide (t = u ∨ t = v ∨ t = w)
  have hgood := hclean x ⟨u, hu, by simp [x]⟩ ⟨v, hv, by simp [x]⟩ (by simp [x])
  have hex : ∃ a b : Fin n, G.Adj a b ∧
      (a = u ∨ a = v ∨ a = w) ∧ (b = u ∨ b = v ∨ b = w) := by
    simpa [graphFun, x] using hgood
  obtain ⟨a, b, hab, ha, hb⟩ := hex
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals first
    | exact G.irrefl hab
    | exact huv hab
    | exact huv hab.symm
    | exact hwu hab
    | exact hwu hab.symm
    | exact hwv hab
    | exact hwv hab.symm

lemma nestedCleaner_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (A B D : Finset (Fin n)) (hA : 2 ≤ (A ∩ D).card) (hB : 2 ≤ (B ∩ D).card)
    {c w : Fin n} (hc : ∀ u ∈ D, G.Adj c u)
    (hclean : ∀ x : Fin n → Bool,
      (∃ u ∈ A, x u = true) → (∃ v ∈ B, x v = true) →
      (∃ t ∈ D, x t = true) → x w = true → graphFun G ∅ x = true) : w = c := by
  apply productCleaner_unique G h4 s hbip (A ∩ D) (B ∩ D) hA hB
    (fun u hu => hc u (Finset.mem_inter.mp hu).2)
    (fun v hv => hc v (Finset.mem_inter.mp hv).2)
  intro x hxA hxB hxw
  obtain ⟨u, hu, hxu⟩ := hxA
  obtain ⟨v, hv, hxv⟩ := hxB
  exact hclean x ⟨u, (Finset.mem_inter.mp hu).1, hxu⟩
    ⟨v, (Finset.mem_inter.mp hv).1, hxv⟩ ⟨u, (Finset.mem_inter.mp hu).2, hxu⟩ hxw

lemma productCleaner_adj_or_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (B : Finset (Fin n)) (hB : 2 ≤ B.card) {c a w : Fin n}
    (hca : G.Adj c a) (hcB : ∀ v ∈ B, G.Adj c v)
    (hclean : ∀ x : Fin n → Bool,
      x a = true → (∃ v ∈ B, x v = true) → x w = true → graphFun G ∅ x = true) :
    w = c ∨ G.Adj w a := by
  classical
  by_cases hw : w = c
  · exact Or.inl hw
  right
  by_contra hwa
  obtain ⟨b, hb, hwb⟩ := exists_nonadjacent G h4 B hB hcB hw
  have hab : ¬ G.Adj a b := neighbors_nonadjacent G s hbip hca (hcB b hb)
  let x : Fin n → Bool := fun t => decide (t = a ∨ t = b ∨ t = w)
  have hgood := hclean x (by simp [x]) ⟨b, hb, by simp [x]⟩ (by simp [x])
  have hex : ∃ u v : Fin n, G.Adj u v ∧
      (u = a ∨ u = b ∨ u = w) ∧ (v = a ∨ v = b ∨ v = w) := by
    simpa [graphFun, x] using hgood
  obtain ⟨u, v, huv, hu, hv⟩ := hex
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  all_goals first
    | exact G.irrefl huv
    | exact hab huv
    | exact hab huv.symm
    | exact hwa huv
    | exact hwa huv.symm
    | exact hwb huv
    | exact hwb huv.symm

lemma nestedCleaner_adj_or_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (A B D : Finset (Fin n)) {a c w : Fin n}
    (ha : a ∈ A ∩ D) (hB : 2 ≤ (B ∩ D).card)
    (hc : ∀ u ∈ D, G.Adj c u)
    (hclean : ∀ x : Fin n → Bool,
      (∃ u ∈ A, x u = true) → (∃ v ∈ B, x v = true) →
      (∃ t ∈ D, x t = true) → x w = true → graphFun G ∅ x = true) :
    w = c ∨ G.Adj w a := by
  apply productCleaner_adj_or_eq G h4 s hbip (B ∩ D) hB
    (hc a (Finset.mem_inter.mp ha).2) (fun v hv => hc v (Finset.mem_inter.mp hv).2)
  intro x hxa hxB hxw
  obtain ⟨v, hv, hxv⟩ := hxB
  exact hclean x ⟨a, (Finset.mem_inter.mp ha).1, hxa⟩
    ⟨v, (Finset.mem_inter.mp hv).1, hxv⟩ ⟨a, (Finset.mem_inter.mp ha).2, hxa⟩ hxw

lemma adjacentCleaner_edge_owned {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (D : Finset (Fin n)) {a c w u v : Fin n}
    (ha : a ∈ D) (hc : ∀ t ∈ D, G.Adj c t)
    (huwv : w = u ∨ w = v) (huv : G.Adj u v) (hD : u ∈ D ∨ v ∈ D)
    (hclean : w = c ∨ G.Adj w a) : c = u ∨ c = v ∨ a = u ∨ a = v := by
  rcases hclean with rfl | hwa
  · rcases huwv with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hstep : ∀ z : Fin n, G.Adj w z → z ∈ D → w = c ∨ z = a := by
    intro z hwz hz
    by_cases hza : z = a
    · exact Or.inr hza
    left
    apply commonCenter_unique G h4 ({a, z} : Finset (Fin n))
    · simp [Finset.card_pair (Ne.symm hza)]
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hwa
      · exact hwz
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with he | he
      · simpa [he] using hc a ha
      · simpa [he] using hc z hz
  rcases huwv with hwu | hwv
  · subst w
    rcases hD with hu | hv
    · exact (neighbors_nonadjacent G s hbip (hc u hu) (hc a ha) hwa).elim
    · rcases hstep v huv hv with h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr (Or.inr h.symm))
  · subst w
    rcases hD with hu | hv
    · rcases hstep u huv.symm hu with h | h
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr (Or.inl h.symm))
    · exact (neighbors_nonadjacent G s hbip (hc v hv) (hc a ha) hwa).elim

lemma nestedCleanedEdge_owned {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (A B D : Finset (Fin n)) {a c w u v : Fin n}
    (ha : a ∈ A ∩ D) (hB : 2 ≤ (B ∩ D).card)
    (hc : ∀ t ∈ D, G.Adj c t)
    (huwv : w = u ∨ w = v) (huv : G.Adj u v) (hD : u ∈ D ∨ v ∈ D)
    (hclean : ∀ x : Fin n → Bool,
      (∃ p ∈ A, x p = true) → (∃ q ∈ B, x q = true) →
      (∃ t ∈ D, x t = true) → x w = true → graphFun G ∅ x = true) :
    c = u ∨ c = v ∨ a = u ∨ a = v := by
  exact adjacentCleaner_edge_owned G h4 s hbip D (Finset.mem_inter.mp ha).2 hc
    huwv huv hD (nestedCleaner_adj_or_eq G h4 s hbip A B D ha hB hc hclean)

lemma triple_forces_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {a b w : Fin n} (haw : ¬ G.Adj a w) (hbw : ¬ G.Adj b w)
    (hgood : graphFun G ∅ (fun t => decide (t = a ∨ t = b ∨ t = w)) = true) :
    G.Adj a b := by
  have hex : ∃ u v : Fin n, G.Adj u v ∧
      (u = a ∨ u = b ∨ u = w) ∧ (v = a ∨ v = b ∨ v = w) := by
    simpa [graphFun] using hgood
  obtain ⟨u, v, huv, hu, hv⟩ := hex
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  all_goals first
    | exact huv
    | exact huv.symm
    | exact (G.irrefl huv).elim
    | exact (haw huv).elim
    | exact (haw huv.symm).elim
    | exact (hbw huv).elim
    | exact (hbw huv.symm).elim

lemma productCleaner_mem_left {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (A B : Finset (Fin n)) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    {c d w : Fin n} (hcA : ∀ u ∈ A, G.Adj c u) (hdB : ∀ v ∈ B, G.Adj d v)
    (hwA : w ∈ A)
    (hclean : ∀ x : Fin n → Bool,
      (∃ u ∈ A, x u = true) → (∃ v ∈ B, x v = true) → x w = true →
      graphFun G ∅ x = true) : w = d := by
  classical
  by_contra hwd
  obtain ⟨b, hb, hwb⟩ := exists_nonadjacent G h4 B hB hdB hwd
  have hbc : b = c := by
    apply commonCenter_unique G h4 A hA _ hcA
    intro a ha
    apply SimpleGraph.Adj.symm
    apply triple_forces_edge G (neighbors_nonadjacent G s hbip (hcA a ha) (hcA w hwA))
      (fun h => hwb h.symm)
    apply hclean
    · exact ⟨a, ha, by simp⟩
    · exact ⟨b, hb, by simp⟩
    · simp
  apply hwb
  rw [hbc]
  exact (hcA w hwA).symm

lemma productCleaner_mem_right {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (A B : Finset (Fin n)) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    {c d w : Fin n} (hcA : ∀ u ∈ A, G.Adj c u) (hdB : ∀ v ∈ B, G.Adj d v)
    (hwB : w ∈ B)
    (hclean : ∀ x : Fin n → Bool,
      (∃ u ∈ A, x u = true) → (∃ v ∈ B, x v = true) → x w = true →
      graphFun G ∅ x = true) : w = c := by
  apply productCleaner_mem_left G h4 s hbip B A hB hA hdB hcA hwB
  intro x hxB hxA hxw
  exact hclean x hxA hxB hxw

lemma nestedCleanedEdge_centers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (A B D : Finset (Fin n)) (hAD : 2 ≤ (A ∩ D).card) (hB : 2 ≤ B.card)
    {c d w u v : Fin n}
    (hcAD : ∀ t ∈ A ∩ D, G.Adj c t) (hdB : ∀ t ∈ B, G.Adj d t)
    (huAD : u ∈ A ∩ D) (hvB : v ∈ B) (huwv : w = u ∨ w = v)
    (hclean : ∀ x : Fin n → Bool,
      (∃ p ∈ A, x p = true) → (∃ q ∈ B, x q = true) →
      (∃ t ∈ D, x t = true) → x w = true → graphFun G ∅ x = true) :
    u = d ∨ v = c := by
  have hprod : ∀ x : Fin n → Bool,
      (∃ p ∈ A ∩ D, x p = true) → (∃ q ∈ B, x q = true) →
      x w = true → graphFun G ∅ x = true := by
    intro x hxAD hxB hxw
    obtain ⟨p, hp, hxp⟩ := hxAD
    exact hclean x ⟨p, (Finset.mem_inter.mp hp).1, hxp⟩ hxB
      ⟨p, (Finset.mem_inter.mp hp).2, hxp⟩ hxw
  rcases huwv with hwu | hwv
  · subst w
    exact Or.inl (productCleaner_mem_left G h4 s hbip (A ∩ D) B hAD hB hcAD hdB huAD hprod)
  · subst w
    exact Or.inr (productCleaner_mem_right G h4 s hbip (A ∩ D) B hAD hB hcAD hdB hvB hprod)

end SharedOrAccounting

namespace SharedProduct

open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
  PEqualNP.Outside.L_meta_5012.SharedOrAccounting

lemma cleaned_edge_has_universal_factor {n m : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (S : Fin m → Finset (Fin n))
    (hmono : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, s u = s v)
    (w v : Fin n) (hwv : G.Adj w v)
    (hpair : ∀ i, w ∈ S i ∨ v ∈ S i)
    (hclean : ∀ x : Fin n → Bool, (∀ i, ∃ u ∈ S i, x u = true) →
      x w = true → graphFun G ∅ x = true) :
    ∃ i, ∀ u ∈ S i, G.Adj w u := by
  classical
  by_contra hnone
  push Not at hnone
  let x : Fin n → Bool := fun t => decide (t = w ∨ (s t ≠ s w ∧ ¬ G.Adj w t))
  have hprod : ∀ i, ∃ u ∈ S i, x u = true := by
    intro i
    by_cases hw : w ∈ S i
    · exact ⟨w, hw, by simp [x]⟩
    · have hv : v ∈ S i := (hpair i).resolve_left hw
      obtain ⟨u, hu, hwu⟩ := hnone i
      have hcolor : s u ≠ s w := by
        intro heq
        exact hbip w v hwv (heq.symm.trans (hmono i u hu v hv))
      exact ⟨u, hu, by simp [x, hcolor, hwu]⟩
  have hgood := hclean x hprod (by simp [x])
  obtain ⟨a, b, hab, ha, hb⟩ : ∃ a b : Fin n, G.Adj a b ∧
      (a = w ∨ (s a ≠ s w ∧ ¬ G.Adj w a)) ∧
      (b = w ∨ (s b ≠ s w ∧ ¬ G.Adj w b)) := by
    simpa [graphFun, x] using hgood
  rcases ha with rfl | ⟨hac, haw⟩ <;> rcases hb with rfl | ⟨hbc, hbw⟩
  · exact G.irrefl hab
  · exact hbw hab
  · exact haw hab.symm
  · have habc := hbip a b hab
    cases hsa : s a <;> cases hsb : s b <;> cases hsw : s w <;> simp_all

lemma cleaned_edge_owned {n m : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (S : Fin m → Finset (Fin n)) (c : Fin m → Fin n)
    (hsize : ∀ i, 2 ≤ (S i).card)
    (hstar : ∀ i, ∀ u ∈ S i, G.Adj (c i) u)
    (w v : Fin n) (hwv : G.Adj w v)
    (hpair : ∀ i, w ∈ S i ∨ v ∈ S i)
    (hclean : ∀ x : Fin n → Bool, (∀ i, ∃ u ∈ S i, x u = true) →
      x w = true → graphFun G ∅ x = true) :
    ∃ i, w = c i ∧ v ∈ S i := by
  have hmono : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, s u = s v := by
    intro i u hu v hv
    have hcu := hbip (c i) u (hstar i u hu)
    have hcv := hbip (c i) v (hstar i v hv)
    cases hsu : s u <;> cases hsv : s v <;> cases hsc : s (c i) <;> simp_all
  obtain ⟨i, hi⟩ := cleaned_edge_has_universal_factor G s hbip S hmono w v hwv hpair hclean
  have hwc : w = c i := commonCenter_unique G h4 (S i) (hsize i) hi (hstar i)
  refine ⟨i, hwc, ?_⟩
  rcases hpair i with hw | hv
  · exact (G.irrefl (hi w hw)).elim
  · exact hv

end SharedProduct

end PEqualNP.Outside.L_meta_5012
