import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

def setOr {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true)

lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  unfold graphFun
  simp

lemma graphFun_pair_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (u v : Fin n) : graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  rw [graphFun_iff]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd hab (G.loopless.irrefl _)
    · exact hab
    · exact hab.symm
    · exact absurd hab (G.loopless.irrefl _)
  · intro huv
    exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

lemma setOr_pair {n : ℕ} (A : Finset (Fin n)) (u v : Fin n) :
    setOr A (pairInput u v) = true ↔ u ∈ A ∨ v ∈ A := by
  simp only [setOr, decide_eq_true_eq, pairInput]
  constructor
  · rintro ⟨a, ha, rfl | rfl⟩
    · exact Or.inl ha
    · exact Or.inr ha
  · rintro (hu | hv)
    · exact ⟨u, hu, Or.inl rfl⟩
    · exact ⟨v, hv, Or.inr rfl⟩

lemma setOr_le_iff {n : ℕ} (A B : Finset (Fin n)) :
    (∀ x : Fin n → Bool, setOr A x = true → setOr B x = true) ↔ A ⊆ B := by
  constructor
  · intro h a ha
    have hv := h (fun v => decide (v = a)) (by
      simp only [setOr, decide_eq_true_eq]
      exact ⟨a, ha, by simp⟩)
    simp only [setOr, decide_eq_true_eq] at hv
    obtain ⟨b, hb, rfl⟩ := hv
    exact hb
  · intro h x hx
    simp only [setOr, decide_eq_true_eq] at hx ⊢
    obtain ⟨a, ha, hxa⟩ := hx
    exact ⟨a, h ha, hxa⟩

namespace Frontier

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
  exact ⟨i, hi, by rw [ite_eq_left hlt]; exact hv⟩

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and)
    (h : ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ W n C x i = true) :
    W n C x (n + r) = true := by
  rw [W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  intro i hi
  rw [ite_eq_left (h i hi).1]; exact (h i hi).2

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

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma orIn_val {n : ℕ} {C : Circuit} {w : ℕ} {u : Fin n}
    (hu : u ∈ orIn n C w) (x : Fin n → Bool) (hxu : x u = true) : W n C x w = true := by
  rcases (orIn_mem n C w u).mp hu with heq | ⟨k, hk, hr, hop, hin⟩
  · rw [← heq, W_input n C x u.val u.isLt]
    exact hxu
  · have hkv : W n C x (n + k) = true := by
      apply W_or n C x k hk hop u.val hin (by have := u.isLt; omega)
      rw [W_input n C x u.val u.isLt]
      exact hxu
    exact reach_up n C x w k hr hkv

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem' C j hj)
  unfold opnd
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => rw [h] at hlen; simp at hlen
  | [_] => rw [h] at hlen; simp at hlen
  | _ :: _ :: _ :: _ => rw [h] at hlen; simp at hlen

lemma gate_op_cases {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
  exact hAO.1 _ (gateAt_mem' C j hj)

end Frontier

namespace RootPatch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm
open Frontier

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
    gateAt (patch C j g) k = gateAt C k := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma W_gate_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (x : Fin n → Bool) {k : ℕ} (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map (W n C x)) := by
  rw [W_gate n C x k hk]
  congr 1
  apply List.map_congr_left
  intro w hw
  rw [ite_eq_left (hAO.2.1 k hk w hw)]

lemma eval_true_mono (gate : Gate) (hop : gate.op = GateOp.and ∨ gate.op = GateOp.or)
    (f h : ℕ → Bool) (hfh : ∀ w ∈ gate.inputs, f w = true → h w = true)
    (hf : gate.op.eval (gate.inputs.map f) = true) :
    gate.op.eval (gate.inputs.map h) = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hf ⊢
    intro w hw
    exact hfh w hw (hf w hw)
  · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hf ⊢
    obtain ⟨w, hw, hfw⟩ := hf
    exact ⟨w, hw, hfh w hw hfw⟩

end RootPatch

namespace AliasCompiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

lemma getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

lemma run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

lemma run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

lemma run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)

def Ok (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ o s t, gs[j] = ⟨o, [s, t]⟩ ∧ (o = GateOp.and ∨ o = GateOp.or) ∧
    s < n + j ∧ t < n + j

lemma ok_snoc {n : ℕ} {gs : List Gate} (h : Ok n gs) {o : GateOp} {s t : ℕ}
    (ho : o = GateOp.and ∨ o = GateOp.or) (hs : s < n + gs.length) (ht : t < n + gs.length) :
    Ok n (gs ++ [⟨o, [s, t]⟩]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]; exact h j hlt
  · have : j = gs.length := by simp at hj; omega
    subst this
    exact ⟨o, s, t, by simp, ho, hs, ht⟩

def ov (gs : List Gate) (x : List Bool) (o : Option ℕ) : Bool :=
  match o with
  | none => false
  | some w => (run gs x).getD w false

lemma ov_ext (gs hs : List Gate) (x : List Bool) (o : Option ℕ)
    (h : ∀ w, o = some w → w < x.length + gs.length) : ov (gs ++ hs) x o = ov gs x o := by
  cases o with
  | none => rfl
  | some w => exact run_prefix gs hs x w (h w rfl)

lemma ov_new (gs : List Gate) (n : ℕ) (x : List Bool) (hx : x.length = n) (o : GateOp) (s t : ℕ)
    (_hs : s < n + gs.length) (_ht : t < n + gs.length) :
    ov (gs ++ [⟨o, [s, t]⟩]) x (some (n + gs.length)) =
      o.eval [(run gs x).getD s false, (run gs x).getD t false] := by
  unfold ov
  simp only
  rw [run_snoc]
  have : n + gs.length = (run gs x).length := by rw [run_length, hx]
  rw [this, getD_at]
  rfl

lemma ok_ao {n : ℕ} {gs : List Gate} {w : ℕ} (hok : Ok n gs) : TopForm.IsAO2 n ⟨gs, w⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; exact h2
  · intro j hj i hi
    obtain ⟨o', s', t', h1, h2, h3, h4⟩ := hok j hj
    have e1 : gateAt ⟨gs, w⟩ j = gs[j] := List.getD_eq_getElem _ _ hj
    rw [e1, h1] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; rfl

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def binaryValue (a : Bool) (s t : Bool) : Bool := if a then s && t else s || t

lemma binary_extend {n : ℕ} {gs : List Gate} (hok : Ok n gs)
    (op : Bool) (a b : Option ℕ)
    (ha : ∀ w, a = some w → w < n+gs.length)
    (hb : ∀ w, b = some w → w < n+gs.length) :
    ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs++hs) ∧ hs.length ≤ 1 ∧
      (∀ w, o = some w → w < n+(gs++hs).length) ∧
      ∀ x : Fin n → Bool, ov (gs++hs) (List.ofFn x) o =
        binaryValue op (ov gs (List.ofFn x) a) (ov gs (List.ofFn x) b) := by
  cases op with
  | false =>
    cases a with
    | none =>
      refine ⟨[], b, by simpa using hok, by simp, by simpa using hb, ?_⟩
      intro x
      simp [binaryValue, ov]
    | some s =>
      cases b with
      | none =>
        refine ⟨[], some s, by simpa using hok, by simp, by simpa using ha, ?_⟩
        intro x
        simp [binaryValue, ov]
      | some t =>
        have hs := ha s rfl
        have ht := hb t rfl
        refine ⟨[⟨GateOp.or,[s,t]⟩], some (n+gs.length), ok_snoc hok (Or.inr rfl) hs ht,
          by simp, ?_, ?_⟩
        · intro w hw
          cases hw
          simp
        · intro x
          rw [ov_new gs n _ (by simp) _ s t hs ht]
          simp [binaryValue, ov, GateOp.eval]
  | true =>
    cases a with
    | none =>
      refine ⟨[], none, by simpa using hok, by simp, by simp, ?_⟩
      intro x
      simp [binaryValue, ov]
    | some s =>
      cases b with
      | none =>
        refine ⟨[], none, by simpa using hok, by simp, by simp, ?_⟩
        intro x
        simp [binaryValue, ov]
      | some t =>
        have hs := ha s rfl
        have ht := hb t rfl
        refine ⟨[⟨GateOp.and,[s,t]⟩], some (n+gs.length), ok_snoc hok (Or.inl rfl) hs ht,
          by simp, ?_, ?_⟩
        · intro w hw
          cases hw
          simp
        · intro x
          rw [ov_new gs n _ (by simp) _ s t hs ht]
          simp [binaryValue, ov, GateOp.eval]

def scheduleValue {n : ℕ} (V : ℕ → (Fin n → Bool) → Bool)
    (op : ℕ → Option Bool) (src : ℕ → Option ℕ) (a b : ℕ → ℕ)
    (j : ℕ) (x : Fin n → Bool) : Bool :=
  match op j with
  | none => match src j with | none => false | some w => V w x
  | some t => binaryValue t (V (a j) x) (V (b j) x)

lemma compile (n : ℕ) (V : ℕ → (Fin n → Bool) → Bool)
    (op : ℕ → Option Bool) (src : ℕ → Option ℕ) (a b : ℕ → ℕ)
    (hin : ∀ w < n, ∀ x, V w x = (List.ofFn x).getD w false) :
    ∀ p,
      (∀ j < p, op j = none → ∀ w, src j = some w → w < n+j) →
      (∀ j < p, op j ≠ none → a j < n+j ∧ b j < n+j) →
      (∀ j < p, ∀ x, V (n+j) x = scheduleValue V op src a b j x) →
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∀ w < n+p, (∀ w', m w = some w' → w' < n+gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) = V w x) ∧
      gs.length ≤ ((Finset.range p).filter fun j => op j ≠ none).card := by
  classical
  intro p
  induction p with
  | zero =>
    intro _ _ _
    refine ⟨[], fun w => some w, by intro j hj; simp at hj, ?_, by simp⟩
    intro w hw
    refine ⟨by intro w' h; cases h; simpa using hw, ?_⟩
    intro x
    rw [hin w (by omega) x]
    rfl
  | succ p ih =>
    intro hsrc hab hV
    obtain ⟨gs,m,hok,hm,hsize⟩ := ih (fun j hj => hsrc j (by omega))
      (fun j hj => hab j (by omega)) (fun j hj => hV j (by omega))
    have hstep : ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs++hs) ∧
        (∀ w, o = some w → w < n+(gs++hs).length) ∧
        (∀ x : Fin n → Bool, ov (gs++hs) (List.ofFn x) o = V (n+p) x) ∧
        hs.length ≤ if op p = none then 0 else 1 := by
      cases hop : op p with
      | none =>
        cases hsp : src p with
        | none =>
          refine ⟨[], none, by simpa using hok, by simp, ?_, by simp⟩
          intro x
          rw [hV p (by omega) x]
          simp [scheduleValue,hop,hsp,ov]
        | some w =>
          have hw := hsrc p (by omega) hop w hsp
          obtain ⟨hmb,hme⟩ := hm w hw
          refine ⟨[], m w, by simpa using hok, by simpa using hmb, ?_, by simp⟩
          intro x
          rw [hV p (by omega) x]
          simp only [scheduleValue,hop,hsp,List.append_nil]
          exact hme x
      | some t =>
        have hn : op p ≠ none := by simp [hop]
        obtain ⟨ha,hb⟩ := hab p (by omega) hn
        obtain ⟨hba,hea⟩ := hm (a p) ha
        obtain ⟨hbb,heb⟩ := hm (b p) hb
        obtain ⟨hs,o,hOk,hLen,hBound,hVal⟩ := binary_extend hok t (m (a p)) (m (b p)) hba hbb
        refine ⟨hs,o,hOk,hBound,?_,by simpa [hop] using hLen⟩
        intro x
        rw [hVal x, hea x, heb x, hV p (by omega) x]
        simp [scheduleValue,hop]
    obtain ⟨hs,o,hOk,hBound,hVal,hLen⟩ := hstep
    refine ⟨gs++hs, Function.update m (n+p) o, hOk, ?_, ?_⟩
    · intro w hw
      by_cases hwp : w = n+p
      · subst w
        rw [Function.update_self]
        exact ⟨hBound,hVal⟩
      · rw [Function.update_of_ne hwp]
        obtain ⟨hmb,hme⟩ := hm w (by omega)
        refine ⟨?_, ?_⟩
        · intro w' hw'
          have hlt := hmb w' hw'
          simp only [List.length_append]
          omega
        · intro x
          rw [ov_ext gs hs _ _ (by simpa using hmb), hme x]
    · rw [Finset.range_add_one, Finset.filter_insert, List.length_append]
      simp only [ne_eq] at hsize
      by_cases hp : op p = none
      · simp only [hp, ne_eq, not_true_eq_false, ↓reduceIte] at hLen ⊢
        omega
      · simp only [hp, ne_eq, not_false_eq_true, ↓reduceIte] at hLen ⊢
        rw [Finset.card_insert_of_notMem (by simp)]
        omega

lemma compile_circuit (n : ℕ) (V : ℕ → (Fin n → Bool) → Bool)
    (op : ℕ → Option Bool) (src : ℕ → Option ℕ) (a b : ℕ → ℕ)
    (hin : ∀ w < n, ∀ x, V w x = (List.ofFn x).getD w false)
    (N : ℕ)
    (hsrc : ∀ j < N, op j = none → ∀ w, src j = some w → w < n+j)
    (hback : ∀ j < N, op j ≠ none → a j < n+j ∧ b j < n+j)
    (hV : ∀ j < N, ∀ x, V (n+j) x = scheduleValue V op src a b j x)
    (out : ℕ) (hout : out < n+N) :
    ∃ C : Circuit, IsAO2 n C ∧
      C.size ≤ ((Finset.range N).filter fun j => op j ≠ none).card ∧
      ∀ x : Fin n → Bool, circuitFun n C x = V out x := by
  obtain ⟨gs,m,hok,hm,hsize⟩ := compile n V op src a b hin N hsrc hback hV
  obtain ⟨_,hsem⟩ := hm out hout
  cases hmo : m out with
  | none =>
    refine ⟨⟨gs,n+gs.length⟩,ok_ao hok,hsize,?_⟩
    intro x
    change (run gs (List.ofFn x)).getD (n+gs.length) false = V out x
    rw [List.getD_eq_default _ _ (by rw [run_length]; simp)]
    have he := hsem x
    simpa only [hmo,ov] using he
  | some w =>
    refine ⟨⟨gs,w⟩,ok_ao hok,hsize,?_⟩
    intro x
    change (run gs (List.ofFn x)).getD w false = V out x
    have he := hsem x
    simpa only [hmo,ov] using he

end AliasCompiler

namespace PrivateProjection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm
open Frontier

lemma W_gate_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (x : Fin n → Bool) {j : ℕ} (hj : j < C.gates.length) :
    W n C x (n+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (W n C x)) := by
  rw [W_gate n C x j hj]
  congr 1
  apply List.map_congr_left
  intro w hw
  rw [ite_eq_left (hAO.2.1 j hj w hw)]

lemma setOr_union {n : ℕ} (A B : Finset (Fin n)) (x : Fin n → Bool) :
    setOr (A ∪ B) x = (setOr A x || setOr B x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [setOr, decide_eq_true_eq, Finset.mem_union, Bool.or_eq_true]
  constructor
  · rintro ⟨a, ha | ha, hx⟩
    · exact Or.inl ⟨a,ha,hx⟩
    · exact Or.inr ⟨a,ha,hx⟩
  · rintro (⟨a,ha,hx⟩ | ⟨a,ha,hx⟩)
    · exact ⟨a,Or.inl ha,hx⟩
    · exact ⟨a,Or.inr ha,hx⟩

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

end PrivateProjection

namespace SingletonPrivacy

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open Frontier

lemma orReach_comp {n : ℕ} {C : Circuit} {r p q : ℕ}
    (hr : r < C.gates.length) (hrp : OrReaches n C (n + r) p)
    (hpq : OrReaches n C (n + p) q) : OrReaches n C (n + r) q := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    have hm : p ∈ (orSets n C).getD r [] := by simpa using hrp.2
    rcases (orSets_mem_iff n C r p hr).mp hm with e | ⟨hop, w, hw, hnw, hwr, hpw⟩
    · subst p
      exact hpq
    · have hpre : OrReaches n C (n + (w - n)) p := by
        exact ⟨by omega, by simpa using hpw⟩
      have hsub := ih (w - n) (by omega) (by omega) hpre
      have he : n + (w - n) = w := by omega
      rw [he] at hsub
      exact orReach_trans n C r hr hop w hw hwr q hsub

lemma setOr_orIn_le_W {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (x : Fin n → Bool) (w : ℕ) (hx : setOr (orIn n C w) x = true) : W n C x w = true := by
  obtain ⟨v, hv, hxv⟩ := of_decide_eq_true hx
  rcases (orIn_mem n C w v).mp hv with h | ⟨k, hk, hwk, hop, hvin⟩
  · rw [← h, W_input n C x v.val v.isLt]
    exact hxv
  · apply reach_up n C x w k hwk
    apply W_or n C x k hk hop v.val hvin (hAO.2.1 k hk v.val hvin)
    rw [W_input n C x v.val v.isLt]
    exact hxv

lemma W_eq_setOr_of_raw {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (w : ℕ) (hraw : ∀ k, k < C.gates.length → OrReaches n C w k →
      (gateAt C k).op = GateOp.or) (x : Fin n → Bool) :
    W n C x w = setOr (orIn n C w) x := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    rcases down n C x (fun k hk => gate_op_cases hAO hk) w hx with h | h
    · simpa only [setOr, decide_eq_true_eq] using h
    · obtain ⟨k, hk, hwk, hop, _⟩ := h
      rw [hraw k hk hwk] at hop
      contradiction
  · exact setOr_orIn_le_W hAO x w

lemma input_reaches_root {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {r p w : ℕ} (hr : r < C.gates.length) (hp : p < C.gates.length)
    (hrp : OrReaches n C (n + r) p) (hop : (gateAt C p).op = GateOp.or)
    (hw : w ∈ (gateAt C p).inputs) (hwn : n ≤ w) :
    w - n < C.gates.length ∧ OrReaches n C (n + r) (w - n) := by
  have hwp := hAO.2.1 p hp w hw
  have hq : w - n < C.gates.length := by omega
  have he : n + (w - n) = w := by omega
  have hself : OrReaches n C w (w - n) := by
    simpa only [he] using (orReach_self n C (w - n) hq)
  exact ⟨hq, orReach_comp hr hrp (orReach_trans n C p hp hop w hw hwp _ hself)⟩

lemma root_descendant_value {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {r p : ℕ} (hr : r < C.gates.length)
    (hrawroot : ∀ k, k < C.gates.length → OrReaches n C (n + r) k →
      (gateAt C k).op = GateOp.or) (hrp : OrReaches n C (n + r) p)
    (x : Fin n → Bool) : W n C x (n + p) = setOr (orIn n C (n + p)) x := by
  apply W_eq_setOr_of_raw hAO
  intro k hk hpk
  exact hrawroot k hk (orReach_comp hr hrp hpk)

lemma orIn_raw_singleton {n : ℕ} (C : Circuit) (v : Fin n) :
    orIn n C v.val = {v} := by
  ext a
  rw [orIn_mem, Finset.mem_singleton]
  constructor
  · rintro (he | ⟨k, hk, hreach, _⟩)
    · exact Fin.ext he
    · have := hreach.1
      omega
  · intro he
    exact Or.inl (congrArg Fin.val he)

end SingletonPrivacy

namespace SingletonFlagProjection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open Frontier PrivateProjection SingletonPrivacy

lemma independent_operand_raw {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {Q : Circuit} (hAO : IsAO2 n Q) (hTF : TopForm G Q)
    {g h w : ℕ} (hgN : g < Q.gates.length) (hgop : (gateAt Q g).op = GateOp.and)
    (hJ : ∀ k, k ∈ junk G Q ↔ k = g ∨ k = h)
    (hhnog : ¬ InCone n Q h g) (hw : w ∈ (gateAt Q g).inputs) :
    ∀ k, k < Q.gates.length → OrReaches n Q w k → (gateAt Q k).op = GateOp.or := by
  intro k hk hreach
  have hc : InCone n Q k g := reach_cone n Q g hgN w hw (hAO.2.1 g hgN w hw) k hreach
  rcases gate_op_cases hAO hk with hkAND | hkOR
  · exfalso
    apply hTF k hk g hgN hkAND _ hgop hc
    intro x hx
    by_contra hf
    have hkJ : k ∈ junk G Q := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hk, hkAND, hk, x, hx, Bool.eq_false_iff.mpr hf⟩
    rcases (hJ k).mp hkJ with he | he
    · have hkg := inCone_lt n Q g k hc
      omega
    · subst k
      exact hhnog hc
  · exact hkOR

end SingletonFlagProjection

namespace H5Support

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm

def gateBit (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def stepWire (w : List Bool) (g : Gate) : List Bool := w ++ [gateBit w g]

def WiresLE (w z : List Bool) : Prop :=
  w.length = z.length ∧ ∀ i, w.getD i false = true → z.getD i false = true

def IsMonoGate (g : Gate) : Prop := g.op = GateOp.and ∨ g.op = GateOp.or

lemma monoGate_of_mem {C : Circuit} (hC : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
    IsMonoGate g := by
  simpa [IsMonoGate] using (hC g hg).1

lemma bit_mono {w z : List Bool} (h : WiresLE w z) {g : Gate} (hg : IsMonoGate g)
    (hw : gateBit w g = true) : gateBit z g = true := by
  rcases hg with hop | hop
  · simp only [gateBit, hop, GateOp.eval, List.all_map, List.all_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    exact fun i hi => h.2 i (hw i hi)
  · simp only [gateBit, hop, GateOp.eval, List.any_map, List.any_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    obtain ⟨i, hi, hv⟩ := hw
    exact ⟨i, hi, h.2 i hv⟩

lemma append_mono {w z : List Bool} {a b : Bool} (h : WiresLE w z)
    (hab : a = true → b = true) : WiresLE (w ++ [a]) (z ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  rw [List.getD_eq_getElem?_getD] at hi ⊢
  by_cases hlt : i < w.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.getElem?_append_left (by rwa [← h.1])]
    simpa only [List.getD_eq_getElem?_getD] using h.2 i
      (by simpa only [List.getD_eq_getElem?_getD] using hi)
  · rw [List.getElem?_append_right (Nat.le_of_not_gt hlt)] at hi
    rw [List.getElem?_append_right (by rw [← h.1]; omega), ← h.1]
    cases hd : i - w.length with
    | zero =>
      simp only [hd, List.getElem?_cons_zero, Option.getD_some] at hi ⊢
      exact hab hi
    | succ k => simp [hd] at hi

lemma fold_mono (gs : List Gate) (hg : ∀ g ∈ gs, IsMonoGate g)
    {w z : List Bool} (h : WiresLE w z) :
    WiresLE (gs.foldl stepWire w) (gs.foldl stepWire z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
      (append_mono h (bit_mono h (hg g (by simp))))

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (stepWire w g) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
    (List.ofFn x).getD u.val false = x u := by
  simp [List.getD_eq_getElem?_getD]

lemma ofFn_mono {n : ℕ} {x y : Fin n → Bool} (h : ∀ u, x u = true → y u = true) :
    WiresLE (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hlt : i < n
  · rw [ofFn_getD y ⟨i, hlt⟩]
    exact h ⟨i, hlt⟩ (by simpa only [ofFn_getD x ⟨i, hlt⟩] using hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hlt)] at hi
    cases hi

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

def earlierWires (C : Circuit) (j : ℕ) (w : List Bool) : List Bool :=
  (C.gates.take j).foldl stepWire w

lemma wires_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (g : Gate) (w : List Bool) :
    (patch C j g).wires w = (C.gates.drop (j + 1)).foldl stepWire (stepWire (earlierWires C j w) g) := by
  change (C.gates.set j g).foldl stepWire w = _
  rw [List.set_eq_take_append_cons_drop, ite_eq_left hj, List.foldl_append, List.foldl_cons]
  rfl

lemma original_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    patch C j C.gates[j] = C := by
  cases C with
  | mk gates output =>
    change Circuit.mk (gates.set j gates[j]) output = Circuit.mk gates output
    congr 1
    exact List.set_getElem_self hj

lemma patch_mono {C : Circuit} (hC : Monotone2 C) {j : ℕ} (hj : j < C.gates.length)
    (g h : Gate) (w : List Bool)
    (hbit : gateBit (earlierWires C j w) g = true → gateBit (earlierWires C j w) h = true) :
    WiresLE ((patch C j g).wires w) ((patch C j h).wires w) := by
  rw [wires_patch hj, wires_patch hj]
  apply fold_mono _ (fun k hk => monoGate_of_mem hC (List.mem_of_mem_drop hk))
  exact append_mono ⟨rfl, fun _ h => h⟩ hbit

lemma patch_bit {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (g : Gate) (x : Fin n → Bool) :
    gateVal n (patch C j g) j x = gateBit (earlierWires C j (List.ofFn x)) g := by
  have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
    unfold earlierWires
    rw [fold_length]
    simp [Nat.min_eq_left (Nat.le_of_lt hj)]
  unfold gateVal
  rw [wires_patch hj, fold_getD_lt _ _ _ (by simp [stepWire, hlen]), ← hlen]
  simp [stepWire, List.getD_eq_getElem?_getD]

lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
    gateAt (patch C j g) k = gateAt C k := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma pair_le {n : ℕ} {x : Fin n → Bool} {u v : Fin n}
    (hu : x u = true) (hv : x v = true) (k : Fin n) :
    pairInput u v k = true → x k = true := by
  simp only [pairInput, decide_eq_true_eq]
  rintro (rfl | rfl)
  · exact hu
  · exact hv

lemma circuit_mono {n : ℕ} {C : Circuit} (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ u, x u = true → y u = true) :
    circuitFun n C x = true → circuitFun n C y = true :=
  (fold_mono C.gates (fun _ hg => monoGate_of_mem hC hg) (ofFn_mono hxy)).2 C.output

lemma mem_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {j : ℕ} :
    j ∈ junk G C ↔ j < C.gates.length ∧ IsDirtyAnd n G C j := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]

lemma ao_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) : Monotone2 C := by
  intro r hr
  exact ⟨by simpa using hAO.1 r hr, (hAO.2.2 r hr).le⟩

lemma patch_gate_ao {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (r : Gate)
    (hrop : IsMonoGate r) (hrlen : r.inputs.length = 2)
    (hrback : ∀ i ∈ r.inputs, i < n + j) : IsAO2 n (patch C j r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    rcases List.mem_or_eq_of_mem_set hq with hq | rfl
    · exact hAO.1 q hq
    · exact hrop
  · intro k hk i hi
    have hkc : k < C.gates.length := by simpa [patch] using hk
    by_cases h : j = k
    · subst k
      have he : gateAt (patch C j r) j = r := by
        simp [gateAt, patch, List.getD_eq_getElem?_getD, hj]
      rw [he] at hi
      exact hrback i hi
    · rw [gateAt_patch_ne C j k r h] at hi
      exact hAO.2.1 k hkc i hi
  · intro q hq
    rcases List.mem_or_eq_of_mem_set hq with hq | rfl
    · exact hAO.2.2 q hq
    · exact hrlen

lemma earlier_read_eq_wireVal {n : ℕ} {C : Circuit} {j w : ℕ}
    (hj : j < C.gates.length) (hw : w < n + j) (x : Fin n → Bool) :
    (earlierWires C j (List.ofFn x)).getD w false = wireVal n C w x := by
  have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
    unfold earlierWires
    rw [fold_length]
    simp [Nat.min_eq_left hj.le]
  calc
    (earlierWires C j (List.ofFn x)).getD w false =
        ((patch C j C.gates[j]).wires (List.ofFn x)).getD w false := by
      rw [wires_patch hj, fold_getD_lt _ _ _ (by simp [stepWire, hlen]; omega)]
      simp [stepWire, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (show w < (earlierWires C j (List.ofFn x)).length by omega)]
    _ = wireVal n C w x := by rw [original_patch hj]; rfl

lemma least_nonempty_graph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (j : ℕ) (hj : j ∈ junk G C) :
    ∃ u v, G.Adj u v := by
  classical
  by_contra hn
  push Not at hn
  let D : Circuit := ⟨[], n⟩
  have hD : IsAO2 n D := by
    simp [IsAO2, AndOrOnly, ReadsBack, D]
  have hDF : circuitFun n D = graphFun G ∅ := by
    funext x
    simp [circuitFun, Circuit.eval, Circuit.wires, D, graphFun, hn,
      List.getD_eq_getElem?_getD]
  have hsize := hL.2.2 D hD hDF
  have hjlen := (mem_junk.mp hj).1
  simp only [Circuit.size, D, List.length_nil] at hsize
  omega

end H5Support

namespace H5Support.Mixed

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
  exact ⟨i, hi, by rw [ite_eq_left hlt]; exact hv⟩

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and)
    (h : ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ W n C x i = true) :
    W n C x (n + r) = true := by
  rw [W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  intro i hi
  rw [ite_eq_left (h i hi).1]; exact (h i hi).2

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

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def monoInput {n : ℕ} (s : Fin n → Bool) (c : Bool) : Fin n → Bool :=
  fun u => decide (s u = c)

lemma monoInput_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v) (c : Bool) :
    graphFun G ∅ (monoInput s c) = false := by
  have hn : ¬ ∃ u v, G.Adj u v ∧ monoInput s c u = true ∧ monoInput s c v = true := by
    rintro ⟨u, v, huv, hu, hv⟩
    have hu' : s u = c := by simpa [monoInput] using hu
    have hv' : s v = c := by simpa [monoInput] using hv
    exact hcol u v huv (hu'.trans hv'.symm)
  simp [graphFun, hn]

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  have hlen := hAO.2.2 _ (gateAt_mem' C a ha)
  unfold opnd
  have hb : b.val < (gateAt C a).inputs.length := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]
  exact List.getElem_mem hb

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a := hAO.2.1 a ha _ (opnd_mem hAO ha b)

lemma mem_inputs_iff_opnd {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {a : ℕ} (ha : a < C.gates.length) (w : ℕ) :
    w ∈ (gateAt C a).inputs ↔ ∃ b : Fin 2, opnd C a b = w := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem' C a ha))
  constructor
  · intro hw
    rw [hin] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨0, by simp [opnd, hin]⟩
    · exact ⟨1, by simp [opnd, hin]⟩
  · rintro ⟨b, rfl⟩
    exact opnd_mem hAO ha b

lemma and_two {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {a : ℕ} (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (b : Fin 2) (x : Fin n → Bool)
    (hb : W n C x (opnd C a b) = true)
    (hc : W n C x (opnd C a (1 - b)) = true) :
    gateVal n C a x = true := by
  apply W_and n C x a ha hand
  intro w hw
  obtain ⟨d, rfl⟩ := (mem_inputs_iff_opnd hAO ha w).mp hw
  refine ⟨opnd_lt hAO ha d, ?_⟩
  have hd : d = b ∨ d = 1 - b := by fin_cases b <;> fin_cases d <;> decide
  rcases hd with rfl | rfl
  · exact hb
  · exact hc

lemma wire_all_true {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w, w < n + C.gates.length → W n C (fun _ => true) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · rw [W_input n C _ w hn]
    · have hk : w - n < C.gates.length := by omega
      have heq : w = n + (w - n) := by omega
      rcases hAO.1 _ (gateAt_mem' C (w - n) hk) with hand | hor
      · rw [heq]
        apply W_and n C _ _ hk hand
        intro i hi
        have hi' := hAO.2.1 (w - n) hk i hi
        exact ⟨hi', ih i (by omega) (by omega)⟩
      · rw [heq]
        apply W_or n C _ _ hk hor (opnd C (w - n) 0)
          (opnd_mem hAO hk 0) (opnd_lt hAO hk 0)
        exact ih _ (by have := opnd_lt hAO hk 0; omega)
          (by have := opnd_lt hAO hk 0; omega)

lemma and_ancestor_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hTop : TopForm G C) {a k : ℕ}
    (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (hk : k < C.gates.length) (hkand : (gateAt C k).op = GateOp.and)
    (hc : InCone n C k a) : k ∈ junk G C := by
  have hnb : ¬ BelowF G C k := fun hb => hTop k hk a ha hkand hb hand hc
  have hd : IsDirtyAnd n G C k := by
    unfold IsDirtyAnd IsDirty
    refine ⟨hkand, hk, ?_⟩
    by_contra he
    apply hnb
    intro x hx
    by_contra hf
    exact he ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hd⟩

lemma W_and_patch {n : ℕ} {C : Circuit} {h : ℕ} (r : Gate) (x : Fin n → Bool)
    (k : ℕ) (hk : k < C.gates.length) (hkop : (gateAt C k).op = GateOp.and)
    (hne : h ≠ k)
    (hall : ∀ w ∈ (gateAt C k).inputs, w < n + k ∧ W n (patch C h r) x w = true) :
    W n (patch C h r) x (n + k) = true := by
  apply W_and n (patch C h r) x k (by simpa [patch] using hk)
  · rw [gateAt_patch_ne C h k r hne]; exact hkop
  · rw [gateAt_patch_ne C h k r hne]; exact hall

lemma and_true_operands {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {t : ℕ} (ht : t < C.gates.length) (hop : (gateAt C t).op = GateOp.and)
    (x : Fin n → Bool) (hv : gateVal n C t x = true) (b : Fin 2) :
    W n C x (opnd C t b) = true := by
  change W n C x (n + t) = true at hv
  rw [W_gate n C x t ht, hop] at hv
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hv
  have hb := hv _ (opnd_mem hAO ht b)
  rwa [ite_eq_left (opnd_lt hAO ht b)] at hb

lemma and_junk_or_below {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {k : ℕ} (hk : k < C.gates.length)
    (hand : (gateAt C k).op = GateOp.and) : k ∈ junk G C ∨ BelowF G C k := by
  by_cases hb : BelowF G C k
  · exact Or.inr hb
  · left
    apply mem_junk.mpr
    refine ⟨hk, hand, hk, ?_⟩
    by_contra he
    apply hb
    intro x hx
    by_contra hf
    exact he ⟨x, hx, Bool.eq_false_iff.mpr hf⟩

lemma orIn_val (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (w : ℕ) (u : Fin n) (hu : u ∈ orIn n C w) (hxu : x u = true) :
    W n C x w = true := by
  rcases (orIn_mem n C w u).mp hu with hu | ⟨k, hk, hr, hkor, huk⟩
  · rw [← hu, W_input n C x u.val u.isLt]
    exact hxu
  · apply reach_up n C x w k hr
    apply W_or n C x k hk hkor u.val huk (by have := u.isLt; omega)
    rw [W_input n C x u.val u.isLt]
    exact hxu

lemma mixed_ne_clean {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {s : Fin n → Bool} (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    {h t : ℕ} (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (htbelow : BelowF G C t) : h ≠ t := by
  rintro rfl
  have hf := htbelow (monoInput s false) (hmix false)
  rw [monoInput_false G s hcol] at hf
  cases hf

lemma output_not_reaches_mixed {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {s : Fin n → Bool} (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hF : circuitFun n C = graphFun G ∅) {h : ℕ}
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true) :
    ¬ OrReaches n C C.output h := by
  intro hr
  have hv := reach_up n C (monoInput s false) C.output h hr (hmix false)
  change circuitFun n C (monoInput s false) = true at hv
  rw [hF, monoInput_false G s hcol] at hv
  cases hv

end H5Support.Mixed

namespace H5Support.MixedOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.H5Support.Mixed

lemma W_or_patch_ne {n : ℕ} {C : Circuit} {e : ℕ} (r : Gate)
    (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hne : e ≠ k) (hkor : (gateAt C k).op = GateOp.or)
    (w : ℕ) (hw : w ∈ (gateAt C k).inputs) (hwlt : w < n + k)
    (hv : W n (patch C e r) x w = true) :
    W n (patch C e r) x (n + k) = true := by
  apply W_or n (patch C e r) x k (by simpa [patch] using hk) _ w _ hwlt hv
  · rw [gateAt_patch_ne C e k r hne]; exact hkor
  · rw [gateAt_patch_ne C e k r hne]; exact hw

lemma reach_val_patch_away {n : ℕ} {C : Circuit} {e : ℕ}
    (r : Gate) (x : Fin n → Bool) (g : ℕ)
    (hv : W n (patch C e r) x (n + g) = true) :
    ∀ k, k < C.gates.length → e ∉ (orSets n C).getD k [] →
      g ∈ (orSets n C).getD k [] → W n (patch C e r) x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hnot hmem
    rcases (orSets_mem_iff n C k g hk).mp hmem with he | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [← he]; exact hv
    · have hne : e ≠ k := fun he => hnot ((orSets_mem_iff n C k e hk).mpr (Or.inl he))
      have hnot' : e ∉ (orSets n C).getD (w - n) [] := by
        intro he
        exact hnot ((orSets_mem_iff n C k e hk).mpr
          (Or.inr ⟨hop, w, hw, hn, hlt, he⟩))
      have h3 := ih (w - n) (by omega) (by omega) hnot' hx
      have heq : n + (w - n) = w := by omega
      rw [heq] at h3
      exact W_or_patch_ne r x k hk hne hop w hw hlt h3

lemma reach_up_patch_away {n : ℕ} {C : Circuit} {e : ℕ}
    (r : Gate) (x : Fin n → Bool) (w g : ℕ)
    (hnot : ¬ OrReaches n C w e)
    (hr : OrReaches n C w g) (hv : W n (patch C e r) x (n + g) = true) :
    W n (patch C e r) x w = true := by
  obtain ⟨hn, hmem⟩ := hr
  by_cases hk : w - n < C.gates.length
  · have hnot' : e ∉ (orSets n C).getD (w - n) [] := fun he => hnot ⟨hn, he⟩
    have h3 := reach_val_patch_away r x g hv (w - n) hk hnot' hmem
    have heq : n + (w - n) = w := by omega
    rwa [heq] at h3
  · exfalso
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets; rw [orFold_length]; simp
    have hge : (orSets n C).length ≤ w - n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
    simp at hmem

lemma orIn_val_patch_away {n : ℕ} {C : Circuit} {e : ℕ}
    (r : Gate) (x : Fin n → Bool) (w : ℕ)
    (hnot : ¬ OrReaches n C w e)
    (u : Fin n) (hu : u ∈ orIn n C w) (hxu : x u = true) :
    W n (patch C e r) x w = true := by
  rcases (orIn_mem n C w u).mp hu with hu | ⟨k, hk, hr, hkor, huk⟩
  · rw [← hu, W_input n (patch C e r) x u.val u.isLt]
    exact hxu
  · have hne : e ≠ k := by rintro rfl; exact hnot hr
    apply reach_up_patch_away r x w k hnot hr
    apply W_or_patch_ne r x k hk hne hkor u.val huk (by have := u.isLt; omega)
    rw [W_input n (patch C e r) x u.val u.isLt]
    exact hxu

end H5Support.MixedOr

namespace H5Support.Mixed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma cone_trans {n : ℕ} {C : Circuit} {i j k : ℕ}
    (hij : InCone n C i j) (hjk : InCone n C j k) : InCone n C i k := by
  induction k using Nat.strong_induction_on generalizing j with
  | _ k ih =>
    obtain ⟨hk, p, hpk, hpin, hjp⟩ := (inCone_iff n C j k).mp hjk
    apply (inCone_iff n C i k).mpr
    refine ⟨hk, p, hpk, hpin, Or.inr ?_⟩
    rcases hjp with he | hjp
    · subst j; exact hij
    · exact ih p hpk hij hjp

lemma no_and_below_independent_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hTop : TopForm G C) {g h : ℕ} (hJ : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) :
    ∀ k, InCone n C k h → (gateAt C k).op ≠ GateOp.and := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  have hhand := (mem_junk.mp hhJ).2.1
  intro k hkh hand
  have hkl := inCone_lt n C h k hkh
  have hkJ := and_ancestor_junk hTop hh hhand (by omega) hand hkh
  have hk : k = g ∨ k = h := by simpa [hJ] using hkJ
  rcases hk with hkg | hkh'
  · subst k; exact hgh hkh
  · omega

def InsideWire (n : ℕ) (C : Circuit) (h w : ℕ) : Prop :=
  w < n ∨ ∃ k, w = n + k ∧ InCone n C k h

lemma operand_inside {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {t h : ℕ} (ht : t < C.gates.length) (hth : t = h ∨ InCone n C t h)
    (w : ℕ) (hw : w ∈ (gateAt C t).inputs) : InsideWire n C h w := by
  by_cases hwn : w < n
  · exact Or.inl hwn
  · right
    have hwt := hAO.2.1 t ht w hw
    have heq : w = n + (w - n) := by omega
    have hct : InCone n C (w - n) t := by
      apply (inCone_iff n C (w - n) t).mpr
      exact ⟨ht, w - n, by omega, by rwa [← heq], Or.inl rfl⟩
    refine ⟨w - n, heq, ?_⟩
    rcases hth with rfl | hth
    · exact hct
    · exact cone_trans hct hth

lemma inside_reached_and {n : ℕ} {C : Circuit} {h w k : ℕ}
    (hinside : InsideWire n C h w) (hr : OrReaches n C w k) : InCone n C k h := by
  rcases hinside with hi | ⟨j, rfl, hjh⟩
  · have := hr.1; omega
  · have hjl := inCone_lt n C h j hjh
    have hh : h < C.gates.length := (inCone_iff n C j h).mp hjh |>.1
    have hmem : k ∈ (orSets n C).getD j [] := by simpa using hr.2
    rcases orSets_cone n C j (by omega) k hmem with heq | hkj
    · subst k; exact hjh
    · exact cone_trans hkj hjh

lemma inside_pure_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {h w : ℕ}
    (hnoand : ∀ k, InCone n C k h → (gateAt C k).op ≠ GateOp.and)
    (hinside : InsideWire n C h w) (x : Fin n → Bool) :
    wireVal n C w x = decide (∃ u ∈ orIn n C w, x u = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro hv
    rcases down n C x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) w hv with
      hr | ⟨k, _, hk, hand, _⟩
    · exact hr
    · exact False.elim (hnoand k (inside_reached_and hinside hk) hand)
  · rintro ⟨u, hu, hxu⟩
    exact orIn_val n C x w u hu hxu

lemma mixed_wire_not_input {n : ℕ} {C : Circuit} {s : Fin n → Bool} {w : ℕ}
    (hmix : ∀ c : Bool, W n C (monoInput s c) w = true) : ¬ w < n := by
  intro hw
  have h0 := hmix false
  have h1 := hmix true
  rw [W_input n C _ w hw] at h0 h1
  simp only [monoInput, decide_eq_true_eq] at h0 h1
  rw [h0] at h1
  cases h1

lemma or_two_value {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {e : ℕ} (he : e < C.gates.length) (heor : (gateAt C e).op = GateOp.or)
    (x : Fin n → Bool) :
    gateVal n C e x = (wireVal n C (opnd C e 0) x || wireVal n C (opnd C e 1) x) := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem' C e he))
  have hp : p < n + e := hAO.2.1 e he p (by simp [hin])
  have hq : q < n + e := hAO.2.1 e he q (by simp [hin])
  change W n C x (n + e) = _
  rw [W_gate n C x e he]
  simp [heor, hin, GateOp.eval, hp, hq, opnd]
  rfl

end H5Support.Mixed

namespace H5Support.Mixed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma pair_same_color_eq {n : ℕ} {G : SimpleGraph (Fin n)} {s : Fin n → Bool}
    (hcol : ∀ a b, G.Adj a b → s a ≠ s b) {a b u v : Fin n} (hab : G.Adj a b)
    (hu : pairInput a b u = true) (hv : pairInput a b v = true) (hcolor : s v = s u) :
    v = u := by
  simp only [pairInput, decide_eq_true_eq] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact hv.trans hu.symm
  · apply False.elim
    apply hcol a b hab
    simpa only [hu, hv] using hcolor.symm
  · apply False.elim
    apply hcol a b hab
    simpa only [hu, hv] using hcolor
  · exact hv.trans hu.symm

lemma or_two_value_oriented {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {e : ℕ} (he : e < C.gates.length) (heor : (gateAt C e).op = GateOp.or)
    (b : Fin 2) (x : Fin n → Bool) :
    gateVal n C e x =
      (wireVal n C (opnd C e b) x || wireVal n C (opnd C e (1 - b)) x) := by
  fin_cases b <;> simpa [Bool.or_comm] using or_two_value hAO he heor x

def copyGate (w : ℕ) : Gate := ⟨GateOp.or, [w, w]⟩

lemma copy_bit {n : ℕ} {C : Circuit} {e w : ℕ}
    (he : e < C.gates.length) (hw : w < n + e) (x : Fin n → Bool) :
    gateBit (earlierWires C e (List.ofFn x)) (copyGate w) = wireVal n C w x := by
  simp only [gateBit, copyGate, GateOp.eval, List.map_cons, List.map_nil,
    List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_self]
  exact earlier_read_eq_wireVal he hw x

lemma original_gate_bit {n : ℕ} {C : Circuit} {e : ℕ}
    (he : e < C.gates.length) (x : Fin n → Bool) :
    gateVal n C e x = gateBit (earlierWires C e (List.ofFn x)) C.gates[e] := by
  have hp := patch_bit he C.gates[e] x
  rwa [original_patch he] at hp

end H5Support.Mixed

namespace H5Support.Splice

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

lemma getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

lemma run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

lemma run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

lemma run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)

def Ok (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ o s t, gs[j] = ⟨o, [s, t]⟩ ∧ (o = GateOp.and ∨ o = GateOp.or) ∧
    s < n + j ∧ t < n + j

lemma ok_snoc {n : ℕ} {gs : List Gate} (h : Ok n gs) {o : GateOp} {s t : ℕ}
    (ho : o = GateOp.and ∨ o = GateOp.or) (hs : s < n + gs.length) (ht : t < n + gs.length) :
    Ok n (gs ++ [⟨o, [s, t]⟩]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]; exact h j hlt
  · have : j = gs.length := by simp at hj; omega
    subst this
    exact ⟨o, s, t, by simp, ho, hs, ht⟩

open Classical in
noncomputable def dc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) : ℕ :=
  ((Finset.range gs.length).filter fun i => (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧
    ∃ x : Fin n → Bool, (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false).card

open Classical in
lemma dc_snoc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) (g : Gate) :
    dc n F (gs ++ [g]) ≤ dc n F gs + if g.op = GateOp.and ∧
      ∃ x : Fin n → Bool, (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = true ∧
        F x = false then 1 else 0 := by
  unfold dc
  rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
  have e : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
    simp [List.getD_eq_getElem?_getD]
  rw [e]
  have h1 : ((Finset.range gs.length).filter fun i =>
      ((gs ++ [g]).getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run (gs ++ [g]) (List.ofFn x)).getD (n + i) false = true ∧ F x = false) =
      (Finset.range gs.length).filter fun i =>
      (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false := by
    refine Finset.filter_congr fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [getD_ltz _ _ _ _ hi']
    refine and_congr_right fun _ => exists_congr fun x => ?_
    rw [run_prefix gs [g] _ _ (by simp; omega)]
  rw [h1]
  split_ifs with h
  · exact (Finset.card_insert_le _ _)
  · simp

def Maps (n p : ℕ) (M : Finset ℕ) (gs : List Gate) (m : ℕ → ℕ)
    (V : (Fin n → Bool) → ℕ → Bool) : Prop :=
  ∀ w < n + p, (w < n ∨ w - n ∉ M) → m w < n + gs.length ∧
    ∀ x : Fin n → Bool, (run gs (List.ofFn x)).getD (m w) false = V x w

def Keeps (n p : ℕ) (Del : Finset ℕ) (gs : List Gate) (m : ℕ → ℕ)
    (op : ℕ → GateOp) : Prop :=
  ∀ j < p, j ∉ Del → ∃ k < gs.length, m (n + j) = n + k ∧
    (gs.getD k ⟨GateOp.or, []⟩).op = op j

lemma append_getD {α : Type} (z : α) (gs hs : List α) (k : ℕ) (hk : k < gs.length) :
    (gs ++ hs).getD k z = gs.getD k z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma next_value (n : ℕ) (gs : List Gate) (o : GateOp) (a b : ℕ)
    (x : Fin n → Bool) :
    (run (gs ++ [⟨o, [a, b]⟩]) (List.ofFn x)).getD (n + gs.length) false =
      o.eval [(run gs (List.ofFn x)).getD a false,
        (run gs (List.ofFn x)).getD b false] := by
  rw [run_snoc]
  have heq : n + gs.length = (run gs (List.ofFn x)).length := by simp [run_length]
  rw [heq, getD_at]
  rfl

open Classical in
lemma build_splice
    (n N h r : ℕ) (M : Finset ℕ) (hnotM : h ∉ M)
    (op : ℕ → GateOp) (a b : ℕ → ℕ)
    (V : (Fin n → Bool) → ℕ → Bool) (F : (Fin n → Bool) → Bool)
    (hin : ∀ x w, w < n → V x w = (List.ofFn x).getD w false)
    (hop : ∀ j < N, op j = GateOp.and ∨ op j = GateOp.or)
    (hback : ∀ j < N, a j < n + j ∧ b j < n + j)
    (havoid : ∀ j < N, j ∉ insert h M →
      (a j < n ∨ a j - n ∉ M) ∧ (b j < n ∨ b j - n ∉ M))
    (hval : ∀ j < N, j ∉ insert h M → ∀ x,
      V x (n + j) = (op j).eval [V x (a j), V x (b j)])
    (block : ∀ (gs : List Gate) (m : ℕ → ℕ), Ok n gs → Maps n h M gs m V →
      ∃ (hs : List Gate) (o : ℕ), Ok n (gs ++ hs) ∧ hs.length ≤ r ∧
        o < n + (gs ++ hs).length ∧
        (∀ x : Fin n → Bool, (run (gs ++ hs) (List.ofFn x)).getD o false = V x (n + h)) ∧
        dc n F (gs ++ hs) ≤ dc n F gs) :
    ∀ p, p ≤ N → ∃ (gs : List Gate) (m : ℕ → ℕ),
      Ok n gs ∧ Maps n p M gs m V ∧ Keeps n p (insert h M) gs m op ∧
      gs.length + ((Finset.range p).filter (· ∈ insert h M)).card ≤
        p + (if h < p then r else 0) ∧
      dc n F gs ≤ ((Finset.range p).filter fun j => j ∉ insert h M ∧ op j = GateOp.and ∧
        ∃ x : Fin n → Bool, V x (n + j) = true ∧ F x = false).card := by
  classical
  intro p
  induction p with
  | zero =>
    intro _
    refine ⟨[], id, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj; simp at hj
    · intro w hw _
      refine ⟨by simpa using hw, fun x => ?_⟩
      exact (hin x w (by simpa using hw)).symm
    · intro j hj; omega
    · simp
    · simp [dc]
  | succ p ih =>
    intro hpN
    obtain ⟨gs, m, hok, hm, hkeep, hlen, hdirty⟩ := ih (by omega)
    have hp : p < N := by omega
    suffices hh : ∃ (hs : List Gate) (o : ℕ), Ok n (gs ++ hs) ∧
        (p ∉ M → o < n + (gs ++ hs).length) ∧
        (p ∉ M → ∀ x : Fin n → Bool,
          (run (gs ++ hs) (List.ofFn x)).getD o false = V x (n + p)) ∧
        (p ∉ insert h M → ∃ k < (gs ++ hs).length, o = n + k ∧
          ((gs ++ hs).getD k ⟨GateOp.or, []⟩).op = op p) ∧
        hs.length + (if p ∈ insert h M then 1 else 0) ≤ 1 + (if p = h then r else 0) ∧
        dc n F (gs ++ hs) ≤ dc n F gs +
          if p ∉ insert h M ∧ op p = GateOp.and ∧
            ∃ x : Fin n → Bool, V x (n + p) = true ∧ F x = false then 1 else 0 by
      obtain ⟨hs, o, h1, h2, h3, h4, h5, h6⟩ := hh
      refine ⟨gs ++ hs, Function.update m (n + p) o, h1, ?_, ?_, ?_, ?_⟩
      · intro w hw hvalid
        by_cases hwp : w = n + p
        · subst w
          rw [Function.update_self]
          have hpm : p ∉ M := by simpa using hvalid
          exact ⟨h2 hpm, h3 hpm⟩
        · rw [Function.update_of_ne hwp]
          obtain ⟨hbound, hvalue⟩ := hm w (by omega) hvalid
          refine ⟨by simp; omega, fun x => ?_⟩
          rw [run_prefix gs hs _ _ (by simpa using hbound)]
          exact hvalue x
      · intro j hj hjDel
        by_cases hjp : j = p
        · subst j
          rw [Function.update_self]
          exact h4 hjDel
        · obtain ⟨k, hk, heq, hopk⟩ := hkeep j (by omega) hjDel
          refine ⟨k, by simp; omega, ?_, ?_⟩
          · rw [Function.update_of_ne (by omega)]
            exact heq
          · rw [append_getD _ _ _ _ hk]
            exact hopk
      · rw [List.length_append, Finset.range_add_one, Finset.filter_insert]
        by_cases hDel : p ∈ insert h M
        · rw [ite_eq_left hDel, Finset.card_insert_of_notMem (by simp)]
          rw [ite_eq_left hDel] at h5
          by_cases hph : p = h
          · subst p
            simp only [lt_self_iff_false, ↓reduceIte, Nat.lt_succ_self] at hlen ⊢
            simp only [↓reduceIte] at h5
            omega
          · have hei : (h < p + 1) ↔ h < p := by omega
            simp only [ite_eq_right hph] at h5
            simp only [hei]
            omega
        · rw [ite_eq_right hDel]
          rw [ite_eq_right hDel] at h5
          have hph : p ≠ h := by intro heq; apply hDel; simp [heq]
          have hei : (h < p + 1) ↔ h < p := by omega
          simp only [ite_eq_right hph] at h5
          simp only [hei]
          omega
      · rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs at h6 ⊢ with hj
        · rw [Finset.card_insert_of_notMem (by simp)]
          omega
        · omega
    by_cases hpM : p ∈ M
    · refine ⟨[], 0, by simpa using hok, fun h => False.elim (h hpM),
        fun h => False.elim (h hpM), ?_, ?_, ?_⟩
      · intro h; exact False.elim (h (Finset.mem_insert_of_mem hpM))
      · have hph : p ≠ h := by intro heq; subst p; exact hnotM hpM
        simp [hpM, hph]
      · simp [hpM]
    by_cases hph : p = h
    · subst p
      obtain ⟨hs, o, hb1, hb2, hb3, hb4, hb5⟩ := block gs m hok hm
      refine ⟨hs, o, hb1, fun _ => hb3, fun _ => hb4, ?_, ?_, ?_⟩
      · simp
      · simp; omega
      · simpa using hb5
    have hpDel : p ∉ insert h M := by simp [hph, hpM]
    obtain ⟨hap, hbp⟩ := hback p hp
    obtain ⟨haValid, hbValid⟩ := havoid p hp hpDel
    obtain ⟨haBound, haValue⟩ := hm (a p) hap haValid
    obtain ⟨hbBound, hbValue⟩ := hm (b p) hbp hbValid
    let g : Gate := ⟨op p, [m (a p), m (b p)]⟩
    have hnew : ∀ x : Fin n → Bool,
        (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = V x (n + p) := by
      intro x
      rw [next_value, haValue x, hbValue x]
      exact (hval p hp hpDel x).symm
    refine ⟨[g], n + gs.length, ok_snoc hok (hop p hp) haBound hbBound, ?_, ?_, ?_, ?_, ?_⟩
    · intro _; simp
    · intro _; exact hnew
    · intro _
      refine ⟨gs.length, by simp, rfl, ?_⟩
      simp [g, List.getD_eq_getElem?_getD]
    · simp [hpDel, hph]
    · have hd := dc_snoc n F gs g
      have heq : (g.op = GateOp.and ∧ ∃ x : Fin n → Bool,
          (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = true ∧ F x = false) ↔
          (p ∉ insert h M ∧ op p = GateOp.and ∧
            ∃ x : Fin n → Bool, V x (n + p) = true ∧ F x = false) := by
        simp only [g, hnew, hpDel, not_false_eq_true, true_and]
      rw [if_congr heq rfl rfl] at hd
      exact hd

lemma ok_isAO2 (n : ℕ) (gs : List Gate) (out : ℕ) (hok : Ok n gs) :
    PEqualNP.TopForm.IsAO2 n ⟨gs, out⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨o, a, b, heq, hop, _, _⟩ := hok j hj
    simpa [heq] using hop
  · intro j hj w hw
    obtain ⟨o, a, b, heq, _, ha, hb⟩ := hok j hj
    have hgate : gateAt (⟨gs, out⟩ : Circuit) j = ⟨o, [a, b]⟩ := by
      change gs.getD j _ = _
      rw [List.getD_eq_getElem _ _ hj]
      exact heq
    rw [hgate] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ha
    · exact hb
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨o, a, b, heq, _, _, _⟩ := hok j hj
    simp [heq]

lemma isAO2_ok (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) :
    Ok n C.gates := by
  intro j hj
  have heq : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hmem : gateAt C j ∈ C.gates := by rw [heq]; exact List.getElem_mem hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hC.2.2 _ hmem)
  refine ⟨(gateAt C j).op, a, b, ?_, hC.1 _ hmem, ?_, ?_⟩
  · rw [← heq]
    have hgate : ∀ (g : Gate), g.inputs = [a, b] → g = ⟨g.op, [a, b]⟩ := by
      intro g hg; cases g; cases hg; rfl
    exact hgate _ hab
  · exact hC.2.1 j hj a (by rw [hab]; simp)
  · exact hC.2.1 j hj b (by rw [hab]; simp)

lemma dc_eq_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) (out : ℕ) :
    dc n (graphFun G ∅) gs = (PEqualNP.TopForm.junk G ⟨gs, out⟩).card := by
  classical
  unfold dc PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hj' : j < gs.length := Finset.mem_range.mp hj
  simp only [PEqualNP.CleanedNonEdge.IsDirtyAnd, PEqualNP.CleanedNonEdge.IsDirty,
    gateAt, PEqualNP.EdgeOwnership.gateVal, Circuit.wires, run, hj', true_and]

open Classical in
lemma splice_complete
    (n N h r : ℕ) (M : Finset ℕ) (hnotM : h ∉ M) (hh : h < N)
    (hM : M ⊆ Finset.range N) (out : ℕ) (hout : out < n + N)
    (houtM : out < n ∨ out - n ∉ M)
    (op : ℕ → GateOp) (a b : ℕ → ℕ)
    (V : (Fin n → Bool) → ℕ → Bool)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hin : ∀ x w, w < n → V x w = (List.ofFn x).getD w false)
    (hop : ∀ j < N, op j = GateOp.and ∨ op j = GateOp.or)
    (hback : ∀ j < N, a j < n + j ∧ b j < n + j)
    (havoid : ∀ j < N, j ∉ insert h M →
      (a j < n ∨ a j - n ∉ M) ∧ (b j < n ∨ b j - n ∉ M))
    (hval : ∀ j < N, j ∉ insert h M → ∀ x,
      V x (n + j) = (op j).eval [V x (a j), V x (b j)])
    (houtput : ∀ x, V x out = graphFun G ∅ x)
    (block : ∀ (gs : List Gate) (m : ℕ → ℕ), Ok n gs → Maps n h M gs m V →
      ∃ (hs : List Gate) (o : ℕ), Ok n (gs ++ hs) ∧ hs.length ≤ r ∧
        o < n + (gs ++ hs).length ∧
        (∀ x : Fin n → Bool, (run (gs ++ hs) (List.ofFn x)).getD o false = V x (n + h)) ∧
        dc n (graphFun G ∅) (gs ++ hs) ≤ dc n (graphFun G ∅) gs) :
    ∃ (D : Circuit) (m : ℕ → ℕ), PEqualNP.TopForm.IsAO2 n D ∧
      circuitFun n D = graphFun G ∅ ∧
      Maps n N M D.gates m V ∧ Keeps n N (insert h M) D.gates m op ∧
      D.size + M.card + 1 ≤ N + r ∧
      (PEqualNP.TopForm.junk G D).card ≤ ((Finset.range N).filter fun j =>
        j ∉ insert h M ∧ op j = GateOp.and ∧
        ∃ x : Fin n → Bool, V x (n + j) = true ∧ graphFun G ∅ x = false).card := by
  obtain ⟨gs, m, hok, hm, hk, hlen, hdc⟩ :=
    build_splice n N h r M hnotM op a b V (graphFun G ∅)
      hin hop hback havoid hval block N le_rfl
  have hDel : ((Finset.range N).filter (· ∈ insert h M)) = insert h M := by
    ext j
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro hj
      refine ⟨?_, hj⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact Finset.mem_range.mpr hh
      · exact hM hj
  rw [hDel, Finset.card_insert_of_notMem hnotM, ite_eq_left hh] at hlen
  refine ⟨⟨gs, m out⟩, m, ok_isAO2 n gs (m out) hok, ?_, hm, hk, ?_, ?_⟩
  · funext x
    exact ((hm out hout houtM).2 x).trans (houtput x)
  · simpa only [Circuit.size, Nat.add_assoc] using hlen
  · rwa [dc_eq_junk G gs (m out)] at hdc

end H5Support.Splice

namespace H5Support.Alias

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.Outside.L_meta_5012.H5Support.Splice

lemma ok_set_alias (n : ℕ) (gs : List Gate) (hok : Ok n gs)
    (j w : ℕ) (hw : w < n + j) :
    Ok n (gs.set j ⟨GateOp.or, [w, w]⟩) := by
  intro k hk
  have hk' : k < gs.length := by simpa using hk
  by_cases hkj : k = j
  · subst k
    refine ⟨GateOp.or, w, w, ?_, Or.inr rfl, hw, hw⟩
    simp
  · obtain ⟨o, a, b, hg, ho, ha, hb⟩ := hok k hk'
    refine ⟨o, a, b, ?_, ho, ha, hb⟩
    rw [List.getElem_set_ne (fun h => hkj h.symm)]
    exact hg

lemma gate_pair {n : ℕ} {C : Circuit} (h : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    C.gates[j] = gateAt C j ∧ (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
    opnd C j 0 < n + j ∧ opnd C j 1 < n + j ∧
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hm : gateAt C j ∈ C.gates := by rw [e]; exact List.getElem_mem hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h.2.2 _ hm)
  have ea : opnd C j 0 = a := by unfold opnd; rw [hab]; rfl
  have eb : opnd C j 1 = b := by unfold opnd; rw [hab]; rfl
  refine ⟨e.symm, by rw [hab, ea, eb], ?_, ?_, h.1 _ hm⟩
  · rw [ea]; exact h.2.1 j hj a (by rw [hab]; simp)
  · rw [eb]; exact h.2.1 j hj b (by rw [hab]; simp)

lemma gate_value {n : ℕ} {C : Circuit} (h : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    (run C.gates (List.ofFn x)).getD (n + j) false =
      (gateAt C j).op.eval [(run C.gates (List.ofFn x)).getD (opnd C j 0) false,
        (run C.gates (List.ofFn x)).getD (opnd C j 1) false] := by
  obtain ⟨heq, hin, ha, hb, _⟩ := gate_pair h hj
  have hh := run_gate C.gates (List.ofFn x) j hj
  rw [List.length_ofFn, heq, hin] at hh
  simpa [ha, hb] using hh

lemma least_output_valid {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length) :
    C.output < n + C.gates.length := by
  by_contra hn
  have hfalse : ∀ x : Fin n → Bool, circuitFun n C x = false := by
    intro x
    apply List.getD_eq_default
    change (run C.gates (List.ofFn x)).length ≤ C.output
    rw [run_length, List.length_ofFn]
    omega
  let D : Circuit := ⟨[], n⟩
  have hD : IsAO2 n D := by simp [IsAO2, PEqualNP.EdgeOwnership.AndOrOnly, ReadsBack, D]
  have hDF : circuitFun n D = graphFun G ∅ := by
    funext x
    rw [← hL.2.1, hfalse]
    simp [D, circuitFun, Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD]
  have hs := hL.2.2 D hD hDF
  simp only [Circuit.size, D, List.length_nil] at hs
  omega

lemma least_patch_alias_impossible {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (e w : ℕ) (he : e < C.gates.length) (hw : w < n + e)
    (hpatch : circuitFun n ⟨C.gates.set e ⟨GateOp.or, [w, w]⟩, C.output⟩ = graphFun G ∅) :
    False := by
  classical
  let P : Circuit := ⟨C.gates.set e ⟨GateOp.or, [w, w]⟩, C.output⟩
  have hP : IsAO2 n P := ok_isAO2 n P.gates P.output
    (ok_set_alias n C.gates (isAO2_ok n C hL.1) e w hw)
  have hlen : P.gates.length = C.gates.length := List.length_set
  have heP : e < P.gates.length := by rwa [hlen]
  let V : (Fin n → Bool) → ℕ → Bool := fun x v => (run P.gates (List.ofFn x)).getD v false
  let op : ℕ → GateOp := fun j => (gateAt P j).op
  let a : ℕ → ℕ := fun j => opnd P j 0
  let b : ℕ → ℕ := fun j => opnd P j 1
  have hin : ∀ x v, v < n → V x v = (List.ofFn x).getD v false := by
    intro x v hv
    exact run_input P.gates (List.ofFn x) v (by simpa using hv)
  have hop : ∀ j < P.gates.length, op j = GateOp.and ∨ op j = GateOp.or := by
    intro j hj
    exact (gate_pair hP hj).2.2.2.2
  have hback : ∀ j < P.gates.length, a j < n + j ∧ b j < n + j := by
    intro j hj
    exact ⟨(gate_pair hP hj).2.2.1, (gate_pair hP hj).2.2.2.1⟩
  have hval : ∀ j < P.gates.length, j ∉ insert e (∅ : Finset ℕ) → ∀ x,
      V x (n + j) = (op j).eval [V x (a j), V x (b j)] := by
    intro j hj _ x
    exact gate_value hP hj x
  have hgate : gateAt P e = ⟨GateOp.or, [w, w]⟩ := by
    simp [P, gateAt, List.getD_eq_getElem?_getD, he]
  have hVe : ∀ x, V x (n + e) = V x w := by
    intro x
    have hh := gate_value hP heP x
    simpa [V, opnd, hgate, GateOp.eval] using hh
  obtain ⟨D, m, hDAO, hDF, _, _, hsize, _⟩ :=
    splice_complete n P.gates.length e 0 ∅ (by simp) heP (by simp) P.output
      (by simpa only [P, List.length_set] using least_output_valid G C hL e he)
      (Or.inr (by simp)) op a b V G hin hop hback (by simp) hval
      (fun x => congrFun hpatch x) (by
        intro gs m hok hm
        have hmW := hm w hw (Or.inr (by simp))
        refine ⟨[], m w, by simpa using hok, by simp, by simpa using hmW.1, ?_, by simp⟩
        intro x
        simpa using (hmW.2 x).trans (hVe x).symm)
  have hmin := hL.2.2 D hDAO hDF
  simp only [Finset.card_empty, Nat.add_zero, hlen] at hsize
  change C.gates.length ≤ D.gates.length at hmin
  change D.gates.length + 1 ≤ C.gates.length at hsize
  omega

end H5Support.Alias

namespace H5Support.Mixed.RawEarliest

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_5012.H5Support.Mixed

lemma reach_comp_gate {n : ℕ} {C : Circuit} {r p q : ℕ}
    (hr : r < C.gates.length) (hrp : OrReaches n C (n + r) p)
    (hpq : OrReaches n C (n + p) q) : OrReaches n C (n + r) q := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    have hm : p ∈ (orSets n C).getD r [] := by simpa using hrp.2
    rcases (orSets_mem_iff n C r p hr).mp hm with e | ⟨hop, w, hw, hnw, hwr, hpw⟩
    · subst p
      exact hpq
    · have hpre : OrReaches n C (n + (w - n)) p := by
        exact ⟨by omega, by simpa using hpw⟩
      have hsub := ih (w - n) (by omega) (by omega) hpre
      have he : n + (w - n) = w := by omega
      rw [he] at hsub
      exact orReach_trans n C r hr hop w hw hwr q hsub

lemma reach_comp {n : ℕ} {C : Circuit} {w p q : ℕ}
    (hw : w < n + C.gates.length) (hwp : OrReaches n C w p)
    (hpq : OrReaches n C (n + p) q) : OrReaches n C w q := by
  have hnw := hwp.1
  have he : n + (w - n) = w := by omega
  have hpre : OrReaches n C (n + (w - n)) p := by simpa only [he] using hwp
  have h := reach_comp_gate (by omega : w - n < C.gates.length) hpre hpq
  simpa only [he] using h

lemma support_subset {n : ℕ} {C : Circuit} {w e : ℕ}
    (hw : w < n + C.gates.length) (hwe : OrReaches n C w e) :
    orIn n C (n + e) ⊆ orIn n C w := by
  intro u hu
  rcases (orIn_mem n C (n + e) u).mp hu with hu | ⟨k, hk, hek, hop, huk⟩
  · have := u.isLt
    omega
  · exact (orIn_mem n C w u).mpr (Or.inr ⟨k, hk, reach_comp hw hwe hek, hop, huk⟩)

lemma side_support_subset {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {e : ℕ} (he : e < C.gates.length) (heor : (gateAt C e).op = GateOp.or)
    (b : Fin 2) : side (n := n) C e b ⊆ orIn n C (n + e) := by
  intro u hu
  rcases (orIn_mem n C (opnd C e b) u).mp hu with hu | ⟨k, hk, hek, hop, huk⟩
  · exact (orIn_mem n C (n + e) u).mpr (Or.inr
      ⟨e, he, orReach_self n C e he, heor, hu ▸ opnd_mem hAO he b⟩)
  · exact (orIn_mem n C (n + e) u).mpr (Or.inr
      ⟨k, hk, orReach_trans n C e he heor _ (opnd_mem hAO he b) (opnd_lt hAO he b) k hek,
        hop, huk⟩)

lemma pure_value {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (w : ℕ)
    (hraw : ∀ k, k < C.gates.length → OrReaches n C w k →
      (gateAt C k).op = GateOp.or) (x : Fin n → Bool) :
    wireVal n C w x = decide (∃ u ∈ orIn n C w, x u = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro hv
    rcases down n C x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) w hv with
      hr | ⟨k, hk, hreach, hand, _⟩
    · exact hr
    · rw [hraw k hk hreach] at hand
      contradiction
  · rintro ⟨u, hu, hxu⟩
    exact orIn_val n C x w u hu hxu

lemma earliest_mixed_raw {n : ℕ} (C : Circuit) (s : Fin n → Bool)
    (hAO : IsAO2 n C) (w : ℕ) (hw : w < n + C.gates.length)
    (hraw : ∀ k, k < C.gates.length → OrReaches n C w k →
      (gateAt C k).op = GateOp.or)
    (hmix : ∀ c : Bool, W n C (monoInput s c) w = true) :
    ∃ e : ℕ, e < C.gates.length ∧ OrReaches n C w e ∧
      (gateAt C e).op = GateOp.or ∧
      (∀ c : Bool, gateVal n C e (monoInput s c) = true) ∧
      orIn n C (n + e) ⊆ orIn n C w ∧
      (∀ b : Fin 2, ∃ c : Bool, wireVal n C (opnd C e b) (monoInput s c) = false) ∧
      (∀ b : Fin 2, (side (n := n) C e b).Nonempty ∧
        side (n := n) C e b ⊆ orIn n C w ∧
        ∀ x : Fin n → Bool, wireVal n C (opnd C e b) x =
          decide (∃ u ∈ side (n := n) C e b, x u = true)) ∧
      ∃ c : Bool, (∀ u ∈ side (n := n) C e 0, s u = c) ∧
        (∀ u ∈ side (n := n) C e 1, s u = !c) := by
  classical
  have hwn : n ≤ w := Nat.le_of_not_gt (mixed_wire_not_input hmix)
  have hstart : ∃ e : ℕ, e < C.gates.length ∧ OrReaches n C w e ∧
      ∀ c : Bool, gateVal n C e (monoInput s c) = true := by
    have heq : w = n + (w - n) := by omega
    refine ⟨w - n, by omega, ?_, ?_⟩
    · rw [heq]
      simpa only [Nat.add_sub_cancel_left] using orReach_self n C (w - n) (by omega)
    · intro c
      have hc := hmix c
      rw [heq] at hc
      exact hc
  let e := Nat.find hstart
  have he : e < C.gates.length := (Nat.find_spec hstart).1
  have hwe : OrReaches n C w e := (Nat.find_spec hstart).2.1
  have hem : ∀ c : Bool, gateVal n C e (monoInput s c) = true := (Nat.find_spec hstart).2.2
  have heor : (gateAt C e).op = GateOp.or := hraw e he hwe
  have hchild (b : Fin 2) (k : ℕ) (hr : OrReaches n C (opnd C e b) k) :
      OrReaches n C w k :=
    reach_comp hw hwe (orReach_trans n C e he heor _
      (opnd_mem hAO he b) (opnd_lt hAO he b) k hr)
  have hnotmixed (b : Fin 2) : ∃ c : Bool,
      wireVal n C (opnd C e b) (monoInput s c) = false := by
    by_contra hn
    push Not at hn
    have hm : ∀ c : Bool, W n C (monoInput s c) (opnd C e b) = true := by
      intro c
      cases hv : wireVal n C (opnd C e b) (monoInput s c) with
      | true => exact hv
      | false => exact False.elim (hn c hv)
    have hnn : n ≤ opnd C e b := Nat.le_of_not_gt (mixed_wire_not_input hm)
    have hlt := opnd_lt hAO he b
    have hkl : opnd C e b - n < C.gates.length := by omega
    have heq : opnd C e b = n + (opnd C e b - n) := by omega
    have hkr : OrReaches n C (opnd C e b) (opnd C e b - n) := by
      conv_lhs => rw [heq]
      exact orReach_self n C _ hkl
    have hkm : ∀ c : Bool, gateVal n C (opnd C e b - n) (monoInput s c) = true := by
      intro c
      have hc := hm c
      rw [heq] at hc
      exact hc
    have hmin : e ≤ opnd C e b - n :=
      Nat.find_min' hstart ⟨hkl, hchild b _ hkr, hkm⟩
    omega
  have hsub := support_subset hw hwe
  have hpure (b : Fin 2) : (side (n := n) C e b).Nonempty ∧
      side (n := n) C e b ⊆ orIn n C w ∧
      ∀ x : Fin n → Bool, wireVal n C (opnd C e b) x =
        decide (∃ u ∈ side (n := n) C e b, x u = true) := by
    have hp := pure_value hAO (opnd C e b) (fun k hk hr => hraw k hk (hchild b k hr))
    refine ⟨?_, Finset.Subset.trans (side_support_subset hAO he heor b) hsub, hp⟩
    have hall := wire_all_true hAO (opnd C e b) (by have := opnd_lt hAO he b; omega)
    change wireVal n C (opnd C e b) (fun _ => true) = true at hall
    rw [hp] at hall
    simpa [Finset.Nonempty, side] using hall
  refine ⟨e, he, hwe, heor, hem, hsub, hnotmixed, hpure, ?_⟩
  obtain ⟨c, hc⟩ := hnotmixed 0
  have h1 : wireVal n C (opnd C e 1) (monoInput s c) = true := by
    have hm := hem c
    rw [or_two_value hAO he heor, hc, Bool.false_or] at hm
    exact hm
  obtain ⟨d, hd⟩ := hnotmixed 1
  have hdc : d ≠ c := by intro hdc; subst d; rw [h1] at hd; cases hd
  have hd' : d = !c := by cases d <;> cases c <;> simp_all
  subst d
  refine ⟨!c, ?_, ?_⟩
  · intro u hu
    have huc : s u ≠ c := by
      intro huc
      have hv := side_val n C (monoInput s c) e 0 u hu (by simp [monoInput, huc])
      change wireVal n C (opnd C e 0) (monoInput s c) = true at hv
      rw [hc] at hv
      cases hv
    cases hsu : s u <;> cases c <;> simp_all
  · intro u hu
    have huc : s u ≠ !c := by
      intro huc
      have hv := side_val n C (monoInput s (!c)) e 1 u hu (by simp [monoInput, huc])
      change wireVal n C (opnd C e 1) (monoInput s (!c)) = true at hv
      rw [hd] at hv
      cases hv
    cases hsu : s u <;> cases c <;> simp_all

lemma earliest_mixed_raw_oriented {n : ℕ} (C : Circuit) (s : Fin n → Bool)
    (hAO : IsAO2 n C) (w : ℕ) (hw : w < n + C.gates.length)
    (hraw : ∀ k, k < C.gates.length → OrReaches n C w k →
      (gateAt C k).op = GateOp.or)
    (hmix : ∀ c : Bool, W n C (monoInput s c) w = true) :
    ∃ (e : ℕ) (b : Fin 2), e < C.gates.length ∧ OrReaches n C w e ∧
      (gateAt C e).op = GateOp.or ∧
      (∀ c : Bool, gateVal n C e (monoInput s c) = true) ∧
      orIn n C (n + e) ⊆ orIn n C w ∧
      (∀ d : Fin 2, (side (n := n) C e d).Nonempty ∧
        side (n := n) C e d ⊆ orIn n C w ∧
        ∀ x : Fin n → Bool, wireVal n C (opnd C e d) x =
          decide (∃ u ∈ side (n := n) C e d, x u = true)) ∧
      (∀ u ∈ side (n := n) C e b, s u = false) ∧
      (∀ u ∈ side (n := n) C e (1 - b), s u = true) := by
  obtain ⟨e, he, hwe, heor, hem, hsub, _, hpure, c, h0, h1⟩ :=
    earliest_mixed_raw C s hAO w hw hraw hmix
  cases c with
  | false =>
    refine ⟨e, 0, he, hwe, heor, hem, hsub, hpure, h0, ?_⟩
    simpa using h1
  | true =>
    refine ⟨e, 1, he, hwe, heor, hem, hsub, hpure, ?_, ?_⟩
    · simpa using h1
    · simpa using h0

end H5Support.Mixed.RawEarliest

namespace SemiMixedSingleton

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.H5Support PEqualNP.Outside.L_meta_5012.H5Support.Mixed
  PEqualNP.Outside.L_meta_5012.H5Support.MixedOr

lemma opposite_of_semimixed_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n  →  Bool) (hcol : ∀ u v, G.Adj u v  →  s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : gateVal n C h (monoInput s false) = true)
    (E : ℕ) (hmixE : ∀ c : Bool, gateVal n C E (monoInput s c) = true)
    (t : ℕ) (ht : t < C.gates.length) (htand : (gateAt C t).op = GateOp.and)
    (htbelow : BelowF G C t) (b : Fin 2) (hreach : OrReaches n C (opnd C t b) E) :
    side (n := n) C t (1 - b) = ∅ ∧
      ¬ OrReaches n C (opnd C t (1 - b)) h ∧
      OrReaches n C (opnd C t (1 - b)) g ∧
      ∀ x : Fin n  →  Bool, wireVal n C (opnd C t (1 - b)) x = gateVal n C g x := by
  have hempty : side (n := n) C t (1 - b) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have hh : W n C (monoInput s (s u)) (opnd C t b) = true :=
      reach_up n C _ _ E hreach (hmixE (s u))
    have ho : W n C (monoInput s (s u)) (opnd C t (1 - b)) = true :=
      side_val n C _ t (1 - b) u hu (by simp [monoInput])
    have htf := htbelow _ (and_two hAO ht htand b _ hh ho)
    rw [monoInput_false G s hcol] at htf
    cases htf
  have hnot : ¬ OrReaches n C (opnd C t (1 - b)) h := by
    intro hr
    have hh : W n C (monoInput s false) (opnd C t b) = true :=
      reach_up n C _ _ E hreach (hmixE false)
    have ho : W n C (monoInput s false) (opnd C t (1 - b)) = true :=
      reach_up n C _ _ h hr hmix
    have htf := htbelow _ (and_two hAO ht htand b _ hh ho)
    rw [monoInput_false G s hcol] at htf
    cases htf
  have hdown (x : Fin n  →  Bool) (hv : W n C x (opnd C t (1 - b)) = true) :
      OrReaches n C (opnd C t (1 - b)) g ∧ gateVal n C g x = true := by
    rcases down n C x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) _ hv with
      ⟨u, hu, _⟩ | ⟨k, hk, hr, hkand, hkv⟩
    · change u ∈ side (n := n) C t (1 - b) at hu
      rw [hempty] at hu
      exact False.elim (Finset.notMem_empty _ hu)
    · have hcone := reach_cone n C t ht _ (opnd_mem hAO ht (1 - b))
        (opnd_lt hAO ht (1 - b)) k hr
      have hkJ := and_ancestor_junk hTop ht htand hk hkand hcone
      have hkg : k = g ∨ k = h := by simpa [hJ] using hkJ
      rcases hkg with hkg | hkg <;> subst k
      · exact ⟨hr, hkv⟩
      · exact False.elim (hnot hr)
  have hr := (hdown (fun _ => true) (wire_all_true hAO _
    (by have := opnd_lt hAO ht (1 - b); omega))).1
  refine ⟨hempty, hnot, hr, ?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact fun hv => (hdown x hv).2
  · exact reach_up n C x _ g hr

lemma clean_and_survives_semimixed_patch {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n  →  Bool) (hcol : ∀ u v, G.Adj u v  →  s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (g h : ℕ) (_hJ : junk G C={g,h})
    (e : ℕ) (hmixE : ∀ c : Bool, gateVal n C e (monoInput s c)=true)
    (r : Gate) (x : Fin n  →  Bool)
    (hpres : ∀ k∈junk G C, gateVal n C k x=true  →  gateVal n (patch C e r) k x=true)
    (hroot : ∀ t, t<C.gates.length  →  (gateAt C t).op=GateOp.and  →  BelowF G C t  → 
      gateVal n C t x=true  →  ∀ b : Fin 2, OrReaches n C (opnd C t b) e  → 
      ∀ w, W n C x w=true  →  W n (patch C e r) x w=true)
    (t : ℕ) (ht : t<C.gates.length) (htand : (gateAt C t).op=GateOp.and)
    (htbelow : BelowF G C t) (hv : gateVal n C t x=true) :
    gateVal n (patch C e r) t x=true := by
  have hne := mixed_ne_clean hcol hmixE htbelow
  by_cases hreach : ∃ b : Fin 2, OrReaches n C (opnd C t b) e
  · obtain ⟨b,hb⟩ := hreach
    exact hroot t ht htand htbelow hv b hb (n+t) hv
  apply W_and_patch r x t ht htand hne
  intro w hw
  obtain ⟨b,rfl⟩ := (mem_inputs_iff_opnd hAO ht w).mp hw
  refine ⟨opnd_lt hAO ht b,?_⟩
  have hnot : ¬ OrReaches n C (opnd C t b) e := fun hb => hreach ⟨b,hb⟩
  have hb := and_true_operands hAO ht htand x hv b
  rcases down n C x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) _ hb with
    ⟨u,hu,hxu⟩ | ⟨k,hk,hr,hkand,hkv⟩
  · exact orIn_val_patch_away r x _ hnot u hu hxu
  · have hcone := reach_cone n C t ht _ (opnd_mem hAO ht b) (opnd_lt hAO ht b) k hr
    have hkJ := and_ancestor_junk hTop ht htand hk hkand hcone
    exact reach_up_patch_away r x _ k hnot hr (hpres k hkJ hkv)

lemma output_survives_semimixed_patch {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n  →  Bool) (hcol : ∀ u v, G.Adj u v  →  s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (hF : circuitFun n C=graphFun G ∅)
    (g h : ℕ) (hJ : junk G C={g,h})
    (e : ℕ) (hmixE : ∀ c : Bool, gateVal n C e (monoInput s c)=true)
    (r : Gate) (x : Fin n  →  Bool)
    (hpres : ∀ k∈junk G C, gateVal n C k x=true  →  gateVal n (patch C e r) k x=true)
    (hroot : ∀ t, t<C.gates.length  →  (gateAt C t).op=GateOp.and  →  BelowF G C t  → 
      gateVal n C t x=true  →  ∀ b : Fin 2, OrReaches n C (opnd C t b) e  → 
      ∀ w, W n C x w=true  →  W n (patch C e r) x w=true)
    (hv : circuitFun n C x=true) : circuitFun n (patch C e r) x=true := by
  have hnot := output_not_reaches_mixed hcol hF hmixE
  rcases down n C x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) C.output hv with
    ⟨u,hu,hxu⟩ | ⟨k,hk,hr,hkand,hkv⟩
  · exact orIn_val_patch_away r x C.output hnot u hu hxu
  · apply reach_up_patch_away r x C.output k hnot hr
    rcases and_junk_or_below (G := G) hk hkand with hkJ | hkbelow
    · exact hpres k hkJ hkv
    · exact clean_and_survives_semimixed_patch G C s hcol hAO hTop g h hJ e hmixE
        r x hpres hroot k hk hkand hkbelow hkv

lemma copy_preserves_of_left_false {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {e : ℕ} (he : e<C.gates.length) (heor : (gateAt C e).op=GateOp.or)
    (b : Fin 2) (x : Fin n  →  Bool)
    (hleft : wireVal n C (opnd C e b) x=false) :
    ∀ w, W n C x w=true  →  W n (patch C e (copyGate (opnd C e (1-b)))) x w=true := by
  have hright := opnd_lt hAO he (1-b)
  have hle := patch_mono (ao_mono hAO) he C.gates[e] (copyGate (opnd C e (1-b)))
    (List.ofFn x) (by
      intro hx
      rw [copy_bit he hright]
      have hroot : gateVal n C e x=true := (original_gate_bit he x).trans hx
      rw [or_two_value_oriented hAO he heor b, hleft, Bool.false_or] at hroot
      exact hroot)
  rw [original_patch he] at hle
  exact hle.2

lemma pure_wire_survives_mixed_patch {n : ℕ} {C : Circuit} {e : ℕ}
    (s : Fin n  →  Bool) (hmixE : ∀ c : Bool, gateVal n C e (monoInput s c)=true)
    (r : Gate) (w : ℕ) (S : Finset (Fin n)) (c : Bool)
    (hS : S=orIn n C w)
    (hsem : ∀ x : Fin n  →  Bool, wireVal n C w x=decide (∃v∈S,x v=true))
    (hcolor : ∀ v∈S,s v=c) (x : Fin n  →  Bool) (hx : W n C x w=true) :
    W n (patch C e r) x w=true := by
  have hnot : ¬ OrReaches n C w e := by
    intro hr
    have hv := reach_up n C (monoInput s (!c)) w e hr (hmixE (!c))
    change wireVal n C w (monoInput s (!c))=true at hv
    rw [hsem] at hv
    obtain ⟨v,hvS,hvc⟩ := of_decide_eq_true hv
    have he : c= !c := (hcolor v hvS).symm.trans (of_decide_eq_true hvc)
    cases c <;> cases he
  change wireVal n C w x=true at hx
  rw [hsem] at hx
  obtain ⟨v,hv,hxv⟩ := of_decide_eq_true hx
  have hvraw : v∈orIn n C w := by simpa only [← hS] using hv
  exact orIn_val_patch_away r x w hnot v hvraw hxv

lemma left_false_of_disjoint_pair {n : ℕ} {G : SimpleGraph (Fin n)}
    {s : Fin n  →  Bool} (hcol : ∀ a b, G.Adj a b  →  s a≠s b)
    (A L : Finset (Fin n)) (hA : ∀a∈A,s a=false) (hL : ∀a∈L,s a=false)
    (hdis : ∀a∈A,a∉L) (a b : Fin n) (hab : G.Adj a b)
    (hsource : ∃v∈A,pairInput a b v=true) :
    decide (∃v∈L,pairInput a b v=true)=false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  obtain ⟨u,hu,hpu⟩ := hsource
  obtain ⟨v,hv,hpv⟩ := of_decide_eq_true hh
  have he : v=u := pair_same_color_eq hcol hab hpu hpv ((hL v hv).trans (hA u hu).symm)
  subst v
  exact hdis u hu hv

lemma left_false_of_clean_filter {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C)
    (s : Fin n  →  Bool) (hcol : ∀a b,G.Adj a b → s a≠s b)
    {e g : ℕ} (he : e<C.gates.length) (heor : (gateAt C e).op=GateOp.or)
    (b : Fin 2) (u : Fin n) (hu : s u=false)
    (hleft : ∀v∈side (n := n) C e b,s v=false)
    (hsem : ∀x,wireVal n C (opnd C e b) x=decide (∃v∈side (n := n) C e b,x v=true))
    (hcenter : ∀x,gateVal n C g x=true → x u=true)
    (hdirty : ∃x,gateVal n C g x=true ∧ graphFun G ∅ x=false)
    (hfilter : ∀x,gateVal n C e x=true → gateVal n C g x=true → graphFun G ∅ x=true)
    (a z : Fin n) (haz : G.Adj a z) (hg : gateVal n C g (pairInput a z)=true) :
    wireVal n C (opnd C e b) (pairInput a z)=false := by
  rw [hsem]
  apply Bool.eq_false_iff.mpr
  intro hh
  obtain ⟨v,hv,hpv⟩ := of_decide_eq_true hh
  have heq : v=u := pair_same_color_eq hcol haz (hcenter _ hg) hpv ((hleft v hv).trans hu.symm)
  subst v
  obtain ⟨x,hgx,hFx⟩ := hdirty
  have hex : gateVal n C e x=true :=
    W_or n C x e he heor _ (opnd_mem hAO he b) (opnd_lt hAO he b)
      (side_val n C x e b u hv (hcenter x hgx))
  have hf := hfilter x hex hgx
  rw [hFx] at hf
  contradiction

lemma alias_patch_computes_of_pairs {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 n C) (hF : circuitFun n C=graphFun G ∅)
    (e w : ℕ) (he : e<C.gates.length) (hw : w<n+e)
    (hunder : ∀x,wireVal n C w x=true → gateVal n C e x=true)
    (hpairs : ∀a b,G.Adj a b → circuitFun n (patch C e (copyGate w)) (pairInput a b)=true) :
    circuitFun n (patch C e (copyGate w))=graphFun G ∅ := by
  let D := patch C e (copyGate w)
  have hDAO : IsAO2 n D := by
    apply patch_gate_ao hAO he
    · exact Or.inr rfl
    · rfl
    · intro i hi
      have hiw : i=w := by simpa [copyGate] using hi
      subst i
      exact hw
  have hdom (x : Fin n  →  Bool) : WiresLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x)) := by
    rw [←original_patch he]
    apply patch_mono (ao_mono hAO) he
    intro hbit
    rw [copy_bit he hw] at hbit
    have hold := hunder x hbit
    rwa [original_gate_bit he] at hold
  funext x
  cases hxF : graphFun G ∅ x with
  | true =>
    obtain ⟨a,b,hab,ha,hb⟩ := (graph_true G x).mp hxF
    exact circuit_mono (ao_mono hDAO) (pair_le ha hb) (hpairs a b hab)
  | false =>
    cases hxD : circuitFun n D x with
    | false => rfl
    | true =>
      have hv : circuitFun n C x=true := (hdom x).2 C.output hxD
      rw [hF,hxF] at hv
      contradiction

lemma no_pure_singleton_semimixed_same_color {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n  →  Bool) (hcol : ∀a b,G.Adj a b → s a≠s b)
    (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hJ : junk G C={g,h})
    (hgh : ¬InCone n C g h) (hhg : ¬InCone n C h g)
    (c d : Fin 2) (u : Fin n) (hgu : side (n := n) C g c={u}) (hu : s u=false)
    (hB : ∀v∈side (n := n) C g (1-c),s v=true)
    (hA : ∀v∈side (n := n) C h d,s v=false)
    (hSleft : ∃v∈side (n := n) C h (1-d),s v=false)
    (hSright : ∃v∈side (n := n) C h (1-d),s v=true)
    (hdis : Disjoint (side (n := n) C h d) (side (n := n) C h (1-d))) : False := by
  have hgJ : g∈junk G C := by simp [hJ]
  have hhJ : h∈junk G C := by simp [hJ]
  obtain ⟨hglen,hgand,_,xg,hgx,hgFx⟩ := mem_junk.mp hgJ
  obtain ⟨hhlen,hhand,_,xh,hhx,hhFx⟩ := mem_junk.mp hhJ
  have hJ' : junk G C={h,g} := by rw [hJ,Finset.pair_comm]
  have hnag := no_and_below_independent_junk hTop hJ' hhg
  have hnah := no_and_below_independent_junk hTop hJ hgh
  have hgraw (b : Fin 2) (x : Fin n  →  Bool) :
      wireVal n C (opnd C g b) x=decide (∃v∈side (n := n) C g b,x v=true) :=
    inside_pure_or hL.1 hnag (operand_inside hL.1 hglen (Or.inl rfl) _ (opnd_mem hL.1 hglen b)) x
  have hhraw (b : Fin 2) (x : Fin n  →  Bool) :
      wireVal n C (opnd C h b) x=decide (∃v∈side (n := n) C h b,x v=true) :=
    inside_pure_or hL.1 hnah (operand_inside hL.1 hhlen (Or.inl rfl) _ (opnd_mem hL.1 hhlen b)) x
  have hcenter (x : Fin n  →  Bool) (hx : gateVal n C g x=true) : x u=true := by
    have hc := and_true_operands hL.1 hglen hgand x hx c
    change wireVal n C (opnd C g c) x=true at hc
    rw [hgraw,hgu] at hc
    simpa using hc
  have hhmono : gateVal n C h (monoInput s false)=true := by
    have had := and_true_operands hL.1 hhlen hhand xh hhx d
    change wireVal n C (opnd C h d) xh=true at had
    rw [hhraw] at had
    obtain ⟨a,ha,_⟩ := of_decide_eq_true had
    obtain ⟨b,hb,hbc⟩ := hSleft
    apply and_two hL.1 hhlen hhand d
    · change wireVal n C (opnd C h d) (monoInput s false)=true
      rw [hhraw]
      exact decide_eq_true ⟨a,ha,by simp [monoInput,hA a ha]⟩
    · change wireVal n C (opnd C h (1-d)) (monoInput s false)=true
      rw [hhraw]
      exact decide_eq_true ⟨b,hb,by simp [monoInput,hbc]⟩
  have hrawS : ∀k,k<C.gates.length → OrReaches n C (opnd C h (1-d)) k → (gateAt C k).op=GateOp.or := by
    intro k hk hr
    rcases hL.1.1 _ (gateAt_mem' C k hk) with hand | hor
    · exact False.elim (hnah k (inside_reached_and
        (operand_inside hL.1 hhlen (Or.inl rfl) _ (opnd_mem hL.1 hhlen (1-d))) hr) hand)
    · exact hor
  have hmixS (b : Bool) : W n C (monoInput s b) (opnd C h (1-d))=true := by
    change wireVal n C (opnd C h (1-d)) (monoInput s b)=true
    rw [hhraw]
    cases b
    · obtain ⟨v,hv,hvc⟩ := hSleft
      exact decide_eq_true ⟨v,hv,by simp [monoInput,hvc]⟩
    · obtain ⟨v,hv,hvc⟩ := hSright
      exact decide_eq_true ⟨v,hv,by simp [monoInput,hvc]⟩
  obtain ⟨e,b,he,hereach,heor,hemix,hesub,hpure,hleft,hright⟩ :=
    RawEarliest.earliest_mixed_raw_oriented C s hL.1 (opnd C h (1-d))
      (by have := opnd_lt hL.1 hhlen (1-d); omega) hrawS hmixS
  let w := opnd C e (1-b)
  let r := copyGate w
  have hw : w<n+e := opnd_lt hL.1 he (1-b)
  have hunder (x : Fin n  →  Bool) (hx : wireVal n C w x=true) : gateVal n C e x=true :=
    W_or n C x e he heor w (opnd_mem hL.1 he (1-b)) hw hx
  have hpairs (a z : Fin n) (haz : G.Adj a z) : circuitFun n (patch C e r) (pairInput a z)=true := by
    let x := pairInput a z
    have hgpres (hxg : gateVal n C g x=true) : gateVal n (patch C e r) g x=true := by
      have heg : e≠g := by intro hh; subst e; rw [hgand] at heor; contradiction
      apply W_and_patch r x g hglen hgand heg
      intro v hv
      obtain ⟨i,rfl⟩ := (mem_inputs_iff_opnd hL.1 hglen v).mp hv
      refine ⟨opnd_lt hL.1 hglen i,?_⟩
      have hcolors : ∃q:Bool,∀v∈side (n := n) C g i,s v=q := by
        by_cases hi : i=c
        · subst i
          refine ⟨false,?_⟩
          intro v hv
          rw [hgu,Finset.mem_singleton] at hv
          simpa only [hv] using hu
        · have hi' : i=1-c := by fin_cases i <;> fin_cases c <;> simp_all
          subst i
          exact ⟨true,hB⟩
      obtain ⟨q,hq⟩ := hcolors
      exact pure_wire_survives_mixed_patch s hemix r _ (side (n := n) C g i) q rfl
        (hgraw i) hq x (and_true_operands hL.1 hglen hgand x hxg i)
    have hhpres (hxh : gateVal n C h x=true) : gateVal n (patch C e r) h x=true := by
      have had := and_true_operands hL.1 hhlen hhand x hxh d
      change wireVal n C (opnd C h d) x=true at had
      rw [hhraw] at had
      have hLf : wireVal n C (opnd C e b) x=false := by
        rw [(hpure b).2.2]
        apply left_false_of_disjoint_pair hcol (side (n := n) C h d) (side (n := n) C e b)
          hA hleft _ a z haz (of_decide_eq_true had)
        intro v hv hvL
        exact Finset.disjoint_left.mp hdis hv ((hpure b).2.1 hvL)
      exact copy_preserves_of_left_false hL.1 he heor b x hLf (n+h) hxh
    apply output_survives_semimixed_patch G C s hcol hL.1 hTop hL.2.1 g h hJ e hemix r x
    · intro k hk hx
      have hk' : k=g∨k=h := by simpa [hJ] using hk
      rcases hk' with rfl | rfl
      · exact hgpres hx
      · exact hhpres hx
    · intro t ht htand htbelow htx i hreach
      obtain ⟨_,_,hrg,heq⟩ := opposite_of_semimixed_gate G C s hcol hL.1 hTop g h hJ
        hhmono e hemix t ht htand htbelow i hreach
      have hgt : gateVal n C g x=true := by
        have ho := and_true_operands hL.1 ht htand x htx (1-i)
        change wireVal n C (opnd C t (1-i)) x=true at ho
        rwa [heq] at ho
      have hfilter (y : Fin n  →  Bool) (hey : gateVal n C e y=true) (hgy : gateVal n C g y=true) :
          graphFun G ∅ y=true :=
        htbelow y (and_two hL.1 ht htand i y
          (reach_up n C y _ e hreach hey) (reach_up n C y _ g hrg hgy))
      have hLf := left_false_of_clean_filter hL.1 s hcol he heor b u hu hleft (hpure b).2.2
        hcenter ⟨xg,hgx,hgFx⟩ hfilter a z haz hgt
      exact copy_preserves_of_left_false hL.1 he heor b x hLf
    · change circuitFun n C (pairInput a z)=true
      rw [hL.2.1]
      exact (graph_true G (pairInput a z)).mpr ⟨a,z,haz,by simp [pairInput],by simp [pairInput]⟩
  have hpatch := alias_patch_computes_of_pairs G C hL.1 hL.2.1 e w he hw hunder hpairs
  exact PEqualNP.Outside.L_meta_5012.H5Support.Alias.least_patch_alias_impossible G C hL e w he hw hpatch

end SemiMixedSingleton

namespace LeftProjectionData

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge

def aliases (J R : Finset ℕ) (a b : ℕ → ℕ) : Finset ℕ :=
  J.filter fun j => a j ∈ R ∨ b j ∈ R

def aliasChild (R : Finset ℕ) (a b : ℕ → ℕ) (j : ℕ) : ℕ :=
  if a j ∈ R then b j else a j

lemma right_sources_le_aliases (J R : Finset ℕ) (a b : ℕ → ℕ)
    (hused : ∀ w ∈ R, ∃ j ∈ J, w = a j ∨ w = b j)
    (hone : ∀ j ∈ J, ¬ (a j ∈ R ∧ b j ∈ R)) :
    R.card ≤ (aliases J R a b).card := by
  classical
  let f : ℕ → ℕ := fun w => if hw : w ∈ R then Classical.choose (hused w hw) else 0
  have hf (w : ℕ) (hw : w ∈ R) : f w ∈ J ∧ (w = a (f w) ∨ w = b (f w)) := by
    simp only [f,dite_eq_left hw]
    exact Classical.choose_spec (hused w hw)
  apply Finset.card_le_card_of_injOn f
  · intro w hw
    have hp := hf w hw
    apply Finset.mem_filter.mpr
    refine ⟨hp.1,?_⟩
    rcases hp.2 with he | he
    · exact Or.inl (he ▸ hw)
    · exact Or.inr (he ▸ hw)
  · intro w hw z hz he
    have hp := hf w hw
    have hq := hf z hz
    rw [← he] at hq
    rcases hp.2 with hwj | hwj <;> rcases hq.2 with hzj | hzj
    · exact hwj.trans hzj.symm
    · exact False.elim (hone (f w) hp.1 ⟨hwj ▸ hw,hzj ▸ hz⟩)
    · exact False.elim (hone (f w) hp.1 ⟨hzj ▸ hz,hwj ▸ hw⟩)
    · exact hwj.trans hzj.symm

lemma union_inter {α : Type*} [DecidableEq α] (S T I : Finset α) :
    (S ∪ T) ∩ I = (S ∩ I) ∪ (T ∩ I) := by
  ext v
  simp only [Finset.mem_union,Finset.mem_inter]
  tauto

lemma left_gate_equation {n j : ℕ} (S : ℕ → Finset (Fin n))
    (I : Finset (Fin n)) (R : Finset ℕ) (a b : ℕ → ℕ)
    (x : Fin n → Bool) (V : ℕ → Bool)
    (hunion : S (n+j) = S (a j) ∪ S (b j))
    (hgate : V (n+j) = setOr (S (n+j) ∩ I) x)
    (hone : ¬ (a j ∈ R ∧ b j ∈ R))
    (hzero : ∀ w, w = a j ∨ w = b j → w ∈ R → S w ∩ I = ∅)
    (hvalue : ∀ w, w = a j ∨ w = b j → w ∉ R → V w = setOr (S w ∩ I) x) :
    V (n+j) = if a j ∈ R then V (b j) else if b j ∈ R then V (a j)
      else V (a j) || V (b j) := by
  rw [hgate,hunion,union_inter,PrivateProjection.setOr_union]
  by_cases ha : a j ∈ R
  · have hb : b j ∉ R := fun hb => hone ⟨ha,hb⟩
    rw [ite_eq_left ha,hzero _ (Or.inl rfl) ha,← hvalue _ (Or.inr rfl) hb]
    simp [setOr]
  · by_cases hb : b j ∈ R
    · rw [ite_eq_right ha,ite_eq_left hb,hzero _ (Or.inr rfl) hb,← hvalue _ (Or.inl rfl) ha]
      simp [setOr]
    · rw [ite_eq_right ha,ite_eq_right hb,← hvalue _ (Or.inl rfl) ha,← hvalue _ (Or.inr rfl) hb]

lemma left_gate_alias {J R : Finset ℕ} {a b : ℕ → ℕ} {j n : ℕ} {V : ℕ → Bool}
    (hj : j ∈ aliases J R a b)
    (heq : V (n+j) = if a j ∈ R then V (b j) else if b j ∈ R then V (a j)
      else V (a j) || V (b j)) : V (n+j) = V (aliasChild R a b j) := by
  rw [heq]
  unfold aliasChild
  by_cases ha : a j ∈ R
  · simp only [ha,ite_true]
  · have hb : b j ∈ R := (Finset.mem_filter.mp hj).2.resolve_left ha
    simp only [ha,hb,ite_false,ite_true]

lemma left_gate_binary {J R : Finset ℕ} {a b : ℕ → ℕ} {j n : ℕ} {V : ℕ → Bool}
    (hj : j ∈ J) (hnot : j ∉ aliases J R a b)
    (heq : V (n+j) = if a j ∈ R then V (b j) else if b j ∈ R then V (a j)
      else V (a j) || V (b j)) : V (n+j) = (V (a j) || V (b j)) := by
  have ha : a j ∉ R := fun ha => hnot (Finset.mem_filter.mpr ⟨hj,Or.inl ha⟩)
  have hb : b j ∉ R := fun hb => hnot (Finset.mem_filter.mpr ⟨hj,Or.inr hb⟩)
  simpa only [ha,hb,ite_false] using heq

lemma right_support_boundary_union {n : ℕ} (J R : Finset ℕ)
    (S : ℕ → Finset (Fin n)) (T : Finset (Fin n)) (a b : ℕ → ℕ)
    (r : ℕ) (hr : r ∈ J)
    (ha : ∀ j ∈ J, a j < n+j) (hb : ∀ j ∈ J, b j < n+j)
    (hunion : ∀ j ∈ J, S (n+j) = S (a j) ∪ S (b j))
    (hboundary : ∀ j ∈ J, ∀ w, w = a j ∨ w = b j →
      ¬ (n ≤ w ∧ w-n ∈ J) → (S w ∩ T).Nonempty → w ∈ R)
    (hRroot : ∀ w ∈ R, S w ⊆ S (n+r))
    (hRright : ∀ w ∈ R, S w ⊆ T) :
    S (n+r) ∩ T = R.biUnion S := by
  have hcover : ∀ j ∈ J, S (n+j) ∩ T ⊆ R.biUnion S := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj v hv
      obtain ⟨hvS,hvT⟩ := Finset.mem_inter.mp hv
      rw [hunion j hj] at hvS
      have child (w : ℕ) (hw : w = a j ∨ w = b j) (hv : v ∈ S w) : v ∈ R.biUnion S := by
        by_cases hins : n ≤ w ∧ w-n ∈ J
        · have hwj : w < n+j := by
            rcases hw with rfl | rfl
            · exact ha j hj
            · exact hb j hj
          have he : n+(w-n) = w := by omega
          exact ih (w-n) (by omega) hins.2 (by simpa only [he] using Finset.mem_inter.mpr ⟨hv,hvT⟩)
        · exact Finset.mem_biUnion.mpr ⟨w,hboundary j hj w hw hins ⟨v,Finset.mem_inter.mpr ⟨hv,hvT⟩⟩,hv⟩
      rcases Finset.mem_union.mp hvS with hv | hv
      · exact child (a j) (Or.inl rfl) hv
      · exact child (b j) (Or.inr rfl) hv
  apply Finset.Subset.antisymm (hcover r hr)
  intro v hv
  obtain ⟨w,hw,hv⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_inter.mpr ⟨hRroot w hw hv,hRright w hw hv⟩

lemma at_most_one_right_child {n : ℕ} (J R : Finset ℕ)
    (S : ℕ → Finset (Fin n)) (I T : Finset (Fin n)) (a b : ℕ → ℕ)
    (hdis : Disjoint I T)
    (hunion : ∀ j ∈ J, S (n+j) = S (a j) ∪ S (b j))
    (hleft : ∀ j ∈ J, (S (n+j) ∩ I).Nonempty)
    (hRright : ∀ w ∈ R, S w ⊆ T) : ∀ j ∈ J, ¬ (a j ∈ R ∧ b j ∈ R) := by
  intro j hj hab
  obtain ⟨v,hv⟩ := hleft j hj
  obtain ⟨hvS,hvI⟩ := Finset.mem_inter.mp hv
  rw [hunion j hj] at hvS
  have hvT : v ∈ T := by
    rcases Finset.mem_union.mp hvS with hv | hv
    · exact hRright (a j) hab.1 hv
    · exact hRright (b j) hab.2 hv
  exact Finset.disjoint_left.mp hdis hvI hvT

lemma right_boundary_nonempty {n : ℕ} (R : Finset ℕ) (S : ℕ → Finset (Fin n))
    (T : Finset (Fin n)) (r : ℕ)
    (heq : S (n+r) ∩ T = R.biUnion S) (hroot : (S (n+r) ∩ T).Nonempty) : R.Nonempty := by
  obtain ⟨v,hv⟩ := hroot
  rw [heq] at hv
  obtain ⟨w,hw,_⟩ := Finset.mem_biUnion.mp hv
  exact ⟨w,hw⟩

end LeftProjectionData

namespace LeftProjectionEval

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open Frontier

noncomputable def value {n : ℕ} (C : Circuit) (J : Finset ℕ)
    (S : ℕ → Finset (Fin n)) (I : Finset (Fin n)) (h p : ℕ) (R : Finset ℕ)
    (x : Fin n → Bool) (w : ℕ) : Bool := by
  classical
  exact if hw : w < n then x ⟨w,hw⟩ else if w-n < C.gates.length then
    if w-n ∈ J then setOr (S w ∩ I) x else if w-n = h then
      (if hp : p < w then value C J S I h p R x p else false) &&
      decide (∃ r ∈ R, (if hr : r < w then value C J S I h p R x r else false) = true)
    else (gateAt C (w-n)).op.eval ((gateAt C (w-n)).inputs.map fun q =>
      if hq : q < w then value C J S I h p R x q else false)
    else false
termination_by w

lemma input {n : ℕ} (C : Circuit) (J : Finset ℕ)
    (S : ℕ → Finset (Fin n)) (I : Finset (Fin n)) (h p : ℕ) (R : Finset ℕ)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    value C J S I h p R x w = x ⟨w,hw⟩ := by
  rw [value]
  simp only [hw,↓reduceDIte]

lemma region {n : ℕ} (C : Circuit) (J : Finset ℕ)
    (S : ℕ → Finset (Fin n)) (I : Finset (Fin n)) (h p : ℕ) (R : Finset ℕ)
    (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) (hjJ : j ∈ J) :
    value C J S I h p R x (n+j) = setOr (S (n+j) ∩ I) x := by
  rw [value]
  simp only [show ¬ n+j < n by omega,↓reduceDIte,Nat.add_sub_cancel_left,hj,hjJ,↓reduceIte]

lemma special {n : ℕ} (C : Circuit) (J : Finset ℕ)
    (S : ℕ → Finset (Fin n)) (I : Finset (Fin n)) (h p : ℕ) (R : Finset ℕ)
    (x : Fin n → Bool) (hh : h < C.gates.length) (hhJ : h ∉ J)
    (hp : p < n+h) (hR : ∀ r ∈ R, r < n+h) :
    value C J S I h p R x (n+h) =
      (value C J S I h p R x p && decide (∃ r ∈ R, value C J S I h p R x r = true)) := by
  rw [value]
  simp only [show ¬ n+h < n by omega,↓reduceDIte,Nat.add_sub_cancel_left,hh,hhJ,↓reduceIte,hp]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨r,hr,hv⟩
    exact ⟨r,hr,by simpa only [hR r hr,↓reduceDIte] using hv⟩
  · rintro ⟨r,hr,hv⟩
    exact ⟨r,hr,by simpa only [hR r hr,↓reduceDIte] using hv⟩

lemma ordinary {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (J : Finset ℕ)
    (S : ℕ → Finset (Fin n)) (I : Finset (Fin n)) (h p : ℕ) (R : Finset ℕ)
    (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) (hjJ : j ∉ J) (hjh : j ≠ h) :
    value C J S I h p R x (n+j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map (value C J S I h p R x)) := by
  rw [value]
  simp only [show ¬ n+j < n by omega,↓reduceDIte,Nat.add_sub_cancel_left,hj,hjJ,hjh,↓reduceIte]
  congr 1
  apply List.map_congr_left
  intro w hw
  simp only [hAO.2.1 j hj w hw,↓reduceDIte]

lemma large {n : ℕ} (C : Circuit) (J : Finset ℕ)
    (S : ℕ → Finset (Fin n)) (I : Finset (Fin n)) (h p : ℕ) (R : Finset ℕ)
    (x : Fin n → Bool) (w : ℕ) (hw : n+C.gates.length ≤ w) :
    value C J S I h p R x w = false := by
  rw [value]
  simp only [show ¬ w<n by omega,show ¬ w-n<C.gates.length by omega,↓reduceDIte,↓reduceIte]

lemma under {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (J : Finset ℕ)
    (S : ℕ → Finset (Fin n)) (I : Finset (Fin n)) (h p q : ℕ) (R : Finset ℕ)
    (hh : h < C.gates.length) (hhJ : h ∉ J) (hhop : (gateAt C h).op = GateOp.and)
    (hhin : (gateAt C h).inputs = [p,q] ∨ (gateAt C h).inputs = [q,p])
    (hR : ∀ r ∈ R, r < n+h)
    (hsemJ : ∀ j < C.gates.length, j ∈ J → ∀ x,
      W n C x (n+j) = setOr (S (n+j)) x)
    (hRcover : ∀ r ∈ R, ∀ x, W n C x r = true → W n C x q = true) :
    ∀ x w, value C J S I h p R x w = true → W n C x w = true := by
  have hp : p < n+h := hAO.2.1 h hh p (by rcases hhin with hi | hi <;> simp [hi])
  intro x w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hv
    by_cases hwn : w < n
    · rw [input C J S I h p R x w hwn] at hv
      rw [W_input n C x w hwn]
      exact hv
    · by_cases hwC : w < n+C.gates.length
      · have hj : w-n < C.gates.length := by omega
        have he : n+(w-n) = w := by omega
        by_cases hjJ : w-n ∈ J
        · have hv' : value C J S I h p R x (n+(w-n)) = true := by simpa only [he] using hv
          rw [region C J S I h p R x _ hj hjJ] at hv'
          rw [← he,hsemJ _ hj hjJ]
          exact (setOr_le_iff (S (n+(w-n)) ∩ I) (S (n+(w-n)))).mpr Finset.inter_subset_left x hv'
        · by_cases hjh : w-n = h
          · have heh : w = n+h := by omega
            subst w
            rw [special C J S I h p R x hh hhJ hp hR] at hv
            simp only [Bool.and_eq_true,decide_eq_true_eq] at hv
            obtain ⟨r,hr,hvr⟩ := hv.2
            have hpval := ih p hp hv.1
            have hqval := hRcover r hr x (ih r (hR r hr) hvr)
            rw [PrivateProjection.W_gate_eq hAO x hh,hhop]
            rcases hhin with hi | hi <;> simp only [hi,List.map_cons,List.map_nil,
              GateOp.eval,List.all_cons,List.all_nil,Bool.and_true,id_eq,hpval,hqval]
          · have hv' : value C J S I h p R x (n+(w-n)) = true := by simpa only [he] using hv
            rw [ordinary hAO J S I h p R x _ hj hjJ hjh] at hv'
            rw [← he,PrivateProjection.W_gate_eq hAO x hj]
            apply RootPatch.eval_true_mono (gateAt C (w-n)) (gate_op_cases hAO hj)
              (value C J S I h p R x) (W n C x) _ hv'
            intro v hv
            have hvw := hAO.2.1 (w-n) hj v hv
            exact ih v (by omega)
      · rw [large C J S I h p R x w (by omega)] at hv
        contradiction

end LeftProjectionEval

namespace SpliceAlias

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open AliasCompiler

noncomputable def leaf (R : Finset ℕ) (i : ℕ) : ℕ := R.toList.getD i 0

noncomputable def chain {n : ℕ} (V : ℕ → (Fin n → Bool) → Bool) (R : Finset ℕ)
    (x : Fin n → Bool) : ℕ → Bool
  | 0 => V (leaf R 0) x
  | k+1 => chain V R x k || V (leaf R (k+1)) x

lemma leaf_mem {R : Finset ℕ} {i : ℕ} (hi : i<R.card) : leaf R i∈R := by
  have hi' : i<R.toList.length := by simpa using hi
  unfold leaf
  rw [List.getD_eq_getElem _ _ hi']
  exact Finset.mem_toList.mp (List.getElem_mem _)

lemma mem_leaf {R : Finset ℕ} {w : ℕ} (hw : w∈R) : ∃i<R.card,leaf R i=w := by
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (Finset.mem_toList.mpr hw)
  refine ⟨i,by simpa using hi,?_⟩
  exact (List.getD_eq_getElem R.toList 0 hi).trans he

lemma chain_true {n : ℕ} (V : ℕ → (Fin n → Bool) → Bool) (R : Finset ℕ)
    (x : Fin n → Bool) (k : ℕ) :
    chain V R x k=true ↔ ∃i≤k,V (leaf R i) x=true := by
  induction k with
  | zero => simp [chain]
  | succ k ih =>
    rw [chain,Bool.or_eq_true,ih]
    constructor
    · rintro (⟨i,hi,hv⟩ | hv)
      · exact ⟨i,by omega,hv⟩
      · exact ⟨k+1,le_rfl,hv⟩
    · rintro ⟨i,hi,hv⟩
      by_cases hik : i≤k
      · exact Or.inl ⟨i,hik,hv⟩
      · have he : i=k+1 := by omega
        exact Or.inr (he ▸ hv)

lemma chain_all {n : ℕ} (V : ℕ → (Fin n → Bool) → Bool) {R : Finset ℕ}
    (hR : R.Nonempty) (x : Fin n → Bool) :
    chain V R x (R.card-1)=decide (∃w∈R,V w x=true) := by
  have hr := Finset.card_pos.mpr hR
  apply Bool.eq_iff_iff.mpr
  rw [chain_true,decide_eq_true_eq]
  constructor
  · rintro ⟨i,hi,hv⟩
    exact ⟨leaf R i,leaf_mem (by omega),hv⟩
  · rintro ⟨w,hw,hv⟩
    obtain ⟨i,hi,rfl⟩ := mem_leaf hw
    exact ⟨i,by omega,hv⟩

def embed (n h L w : ℕ) : ℕ := if w<n+h then w else w+L

noncomputable def expanded {n : ℕ} (V : ℕ → (Fin n → Bool) → Bool)
    (h : ℕ) (R : Finset ℕ) (w : ℕ) (x : Fin n → Bool) : Bool :=
  if w<n+h then V w x
  else if w<n+h+(R.card-1) then chain V R x (w-(n+h)+1)
  else V (w-(R.card-1)) x

lemma expanded_before {n : ℕ} (V : ℕ → (Fin n → Bool) → Bool)
    (h : ℕ) (R : Finset ℕ) {w : ℕ} (hw : w<n+h) (x : Fin n → Bool) :
    expanded V h R w x=V w x := by simp [expanded,hw]

lemma expanded_embed {n : ℕ} (V : ℕ → (Fin n → Bool) → Bool)
    (h : ℕ) (R : Finset ℕ) (w : ℕ) (x : Fin n → Bool) :
    expanded V h R (embed n h (R.card-1) w) x=V w x := by
  by_cases hw : w<n+h
  · simp [embed,expanded,hw]
  · have hn : ¬w+(R.card-1)<n+h := by omega
    have hn' : ¬w+(R.card-1)<n+h+(R.card-1) := by omega
    simp [embed,expanded,hw,hn,hn']

lemma expanded_chain {n : ℕ} (V : ℕ → (Fin n → Bool) → Bool)
    (h : ℕ) (R : Finset ℕ) {k : ℕ} (hk : k<R.card-1) (x : Fin n → Bool) :
    expanded V h R (n+h+k) x=chain V R x (k+1) := by
  have h0 : ¬n+h+k<n+h := by omega
  have h1 : n+h+k<n+h+(R.card-1) := by omega
  simp [expanded,h0,h1]

lemma embed_back {n h L i w : ℕ} (_hi : h ≤ i) (hw : w<n+i) :
    embed n h L w<n+(i+L) := by
  unfold embed
  split_ifs <;> omega

noncomputable def rightRoot (n h : ℕ) (R : Finset ℕ) : ℕ :=
  if R.card=1 then leaf R 0 else n+h+(R.card-1)-1

lemma rightRoot_back {n h : ℕ} {R : Finset ℕ} (hR : R.Nonempty)
    (hback : ∀w∈R,w<n+h) : rightRoot n h R<n+(h+(R.card-1)) := by
  have hr := Finset.card_pos.mpr hR
  by_cases he : R.card=1
  · have hb := hback (leaf R 0) (leaf_mem (by omega))
    simp only [rightRoot,he,ite_true]
    omega
  · simp only [rightRoot,he,ite_false]
    omega

lemma rightRoot_value {n : ℕ} (V : ℕ → (Fin n → Bool) → Bool) {h : ℕ} {R : Finset ℕ}
    (hR : R.Nonempty) (hback : ∀w∈R,w<n+h) (x : Fin n → Bool) :
    expanded V h R (rightRoot n h R) x=decide (∃w∈R,V w x=true) := by
  have hr := Finset.card_pos.mpr hR
  rw [←chain_all V hR x]
  by_cases he : R.card=1
  · have hb := hback (leaf R 0) (leaf_mem (by omega))
    simp [rightRoot,he,expanded_before V h R hb x,chain]
  · have hk : R.card-1-1<R.card-1 := by omega
    have hw : n+h+(R.card-1)-1=n+h+(R.card-1-1) := by omega
    have hkk : R.card-1-1+1=R.card-1 := by omega
    rw [rightRoot,ite_eq_right he,hw,expanded_chain V h R hk x,hkk]

lemma expanded_old_gate {n : ℕ} (V : ℕ → (Fin n → Bool) → Bool)
    (h : ℕ) (R : Finset ℕ) {i : ℕ} (hi : h ≤ i) (x : Fin n → Bool) :
    expanded V h R (n+(i+(R.card-1))) x=V (n+i) x := by
  have hh : ¬n+i<n+h := by omega
  simpa only [embed,hh,ite_false,Nat.add_assoc] using expanded_embed V h R (n+i) x

noncomputable def spliceOp (h : ℕ) (R A : Finset ℕ) (op : ℕ → Bool) (j : ℕ) : Option Bool :=
  if j∈A then none else some
    (if j<h then op j else if j<h+(R.card-1) then false
     else if j=h+(R.card-1) then true else op (j-(R.card-1)))

noncomputable def spliceA (n h p : ℕ) (R : Finset ℕ) (a : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j<h then a j else if j<h+(R.card-1) then
    (if j=h then leaf R 0 else n+j-1)
  else if j=h+(R.card-1) then p else embed n h (R.card-1) (a (j-(R.card-1)))

noncomputable def spliceB (n h : ℕ) (R : Finset ℕ) (b : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j<h then b j else if j<h+(R.card-1) then leaf R (j-h+1)
  else if j=h+(R.card-1) then rightRoot n h R else embed n h (R.card-1) (b (j-(R.card-1)))

lemma splice_back {n N h p : ℕ} {R : Finset ℕ} {a b : ℕ → ℕ}
    (hR : R.Nonempty) (hRb : ∀w∈R,w<n+h) (hp : p<n+h) (hhN : h ≤ N)
    (hab : ∀j<N,a j<n+j∧b j<n+j)
    {j : ℕ} (hj : j<N+(R.card-1)) :
    spliceA n h p R a j<n+j ∧ spliceB n h R b j<n+j := by
  have hr := Finset.card_pos.mpr hR
  by_cases hjh : j<h
  · have hjN : j<N := by omega
    simpa only [spliceA,spliceB,hjh,ite_true] using hab j hjN
  · by_cases hjc : j<h+(R.card-1)
    · have hi : j-h+1<R.card := by omega
      have hb := hRb (leaf R (j-h+1)) (leaf_mem hi)
      simp only [spliceA,spliceB,hjh,ite_false,hjc,ite_true]
      refine ⟨?_,by omega⟩
      by_cases he : j=h
      · have ha := hRb (leaf R 0) (leaf_mem (by omega))
        rw [ite_eq_left he]
        omega
      · rw [ite_eq_right he]
        omega
    · by_cases he : j=h+(R.card-1)
      · simp only [spliceA,spliceB,ite_eq_right hjh,ite_eq_right hjc,ite_eq_left he]
        exact ⟨by omega,by simpa only [he] using rightRoot_back hR hRb⟩
      · have hi : j-(R.card-1)<N := by omega
        have hh : h ≤ j-(R.card-1) := by omega
        have he' : j-(R.card-1)+(R.card-1)=j := by omega
        obtain ⟨ha,hb⟩ := hab (j-(R.card-1)) hi
        simp only [spliceA,spliceB,hjh,ite_false,hjc,he]
        constructor
        · simpa only [he'] using embed_back (L := R.card-1) hh ha
        · simpa only [he'] using embed_back (L := R.card-1) hh hb

lemma inserted_left_value {n : ℕ} (V : ℕ → (Fin n → Bool) → Bool)
    {h p : ℕ} {R : Finset ℕ} {a : ℕ → ℕ}
    (hR : R.Nonempty) (hRb : ∀w∈R,w<n+h)
    {j : ℕ} (hj : h ≤ j) (hjc : j<h+(R.card-1)) (x : Fin n → Bool) :
    expanded V h R (spliceA n h p R a j) x=chain V R x (j-h) := by
  have hr := Finset.card_pos.mpr hR
  have hjh : ¬j<h := by omega
  simp only [spliceA,hjh,ite_false,hjc,ite_true]
  by_cases he : j=h
  · subst j
    have hleaf := hRb (leaf R 0) (leaf_mem (by omega))
    simp [expanded_before V h R hleaf x,chain]
  · have hi : j-h-1<R.card-1 := by omega
    have hew : n+j-1=n+h+(j-h-1) := by omega
    have hek : j-h-1+1=j-h := by omega
    rw [ite_eq_right he,hew,expanded_chain V h R hi x,hek]

lemma splice_value {n N h p : ℕ} {R A : Finset ℕ} {op : ℕ → Bool}
    {a b link : ℕ → ℕ} (V : ℕ → (Fin n → Bool) → Bool)
    (hR : R.Nonempty) (hRb : ∀w∈R,w<n+h) (hp : p<n+h) (hhN : h ≤ N)
    (hAb : ∀j∈A,j<h) (hab : ∀j<N,a j<n+j∧b j<n+j)
    (haliasb : ∀j∈A,link j<n+j)
    (halias : ∀j∈A,∀x,V (n+j) x=V (link j) x)
    (hval : ∀j<N,j∉A→j≠h→∀x,
      V (n+j) x=binaryValue (op j) (V (a j) x) (V (b j) x))
    (hpatch : ∀x,V (n+h) x=(V p x&&decide (∃w∈R,V w x=true)))
    {j : ℕ} (hj : j<N+(R.card-1)) (x : Fin n → Bool) :
    expanded V h R (n+j) x=
      scheduleValue (expanded V h R) (spliceOp h R A op) (fun i=>some (link i))
        (spliceA n h p R a) (spliceB n h R b) j x := by
  by_cases hjA : j∈A
  · have hjh := hAb j hjA
    have haj := haliasb j hjA
    have hgate : n+j<n+h := by omega
    have hals : link j<n+h := by omega
    simp only [scheduleValue,spliceOp,hjA,ite_true]
    rw [expanded_before V h R hgate x,expanded_before V h R hals x]
    exact halias j hjA x
  · by_cases hjh : j<h
    · have hjN : j<N := by omega
      obtain ⟨ha,hb⟩ := hab j hjN
      have hgate : n+j<n+h := by omega
      have has : a j<n+h := by omega
      have hbs : b j<n+h := by omega
      simp only [scheduleValue,spliceOp,spliceA,spliceB,hjA,ite_false,hjh,ite_true]
      rw [expanded_before V h R hgate x,expanded_before V h R has x,
        expanded_before V h R hbs x]
      exact hval j hjN hjA (by omega) x
    · by_cases hjc : j<h+(R.card-1)
      · have hh : h ≤ j := by omega
        have hi : j-h<R.card-1 := by omega
        have hw : n+j=n+h+(j-h) := by omega
        have hleaf := hRb (leaf R (j-h+1)) (leaf_mem (by omega))
        simp only [scheduleValue,spliceOp,hjA,ite_false,hjh,hjc,ite_true,binaryValue,Bool.false_eq_true]
        rw [inserted_left_value V hR hRb hh hjc x]
        simp only [spliceB,hjh,ite_false,hjc,ite_true]
        rw [expanded_before V h R hleaf x,hw,expanded_chain V h R hi x]
        rfl
      · by_cases he : j=h+(R.card-1)
        · subst j
          have h0 : ¬h+(R.card-1)<h := by omega
          simp only [scheduleValue,spliceOp,spliceA,spliceB,hjA,ite_false,h0,lt_self_iff_false,ite_true,binaryValue]
          rw [expanded_old_gate V h R (le_refl h) x,expanded_before V h R hp x,rightRoot_value V hR hRb x]
          exact hpatch x
        · have hi : j-(R.card-1)<N := by omega
          have hh : h ≤ j-(R.card-1) := by omega
          have hiA : j-(R.card-1)∉A := by intro hm; have := hAb _ hm; omega
          have hih : j-(R.card-1)≠h := by omega
          have hjold : j=(j-(R.card-1))+(R.card-1) := by omega
          simp only [scheduleValue,spliceOp,spliceA,spliceB,hjA,ite_false,hjh,hjc,he]
          rw [expanded_embed,expanded_embed]
          conv_lhs => rw [hjold]
          rw [expanded_old_gate V h R hh x]
          exact hval _ hi hiA hih x

lemma compile_splice (n N h p : ℕ) (op : ℕ → Bool) (a b link : ℕ → ℕ)
    (R A : Finset ℕ) (V : ℕ → (Fin n → Bool) → Bool)
    (hh : h<N) (hR : R.Nonempty) (hRb : ∀w∈R,w<n+h) (hp : p<n+h)
    (hAb : ∀j∈A,j<h) (hcount : R.card≤A.card)
    (hab : ∀j<N,a j<n+j∧b j<n+j) (haliasb : ∀j∈A,link j<n+j)
    (hin : ∀w<n,∀x,V w x=(List.ofFn x).getD w false)
    (halias : ∀j∈A,∀x,V (n+j) x=V (link j) x)
    (hval : ∀j<N,j∉A→j≠h→∀x,
      V (n+j) x=binaryValue (op j) (V (a j) x) (V (b j) x))
    (hpatch : ∀x,V (n+h) x=(V p x&&decide (∃w∈R,V w x=true)))
    (out : ℕ) (hout : out<n+N) :
    ∃E : Circuit,IsAO2 n E∧E.size<N∧∀x,circuitFun n E x=V out x := by
  have hInput : ∀w<n,∀x,expanded V h R w x=(List.ofFn x).getD w false := by
    intro w hw x
    rw [expanded_before V h R (by omega) x]
    exact hin w hw x
  have hAlias : ∀j<N+(R.card-1),spliceOp h R A op j=none→
      ∀w,(some (link j):Option ℕ)=some w→w<n+j := by
    intro j hj hno w he
    have hjA : j∈A := by by_contra hn; simp [spliceOp,hn] at hno
    have he' : link j=w := Option.some.inj he
    rw [←he']
    exact haliasb j hjA
  have hBack : ∀j<N+(R.card-1),spliceOp h R A op j≠none→
      spliceA n h p R a j<n+j∧spliceB n h R b j<n+j := by
    intro j hj _
    exact splice_back hR hRb hp (Nat.le_of_lt hh) hab hj
  have hValue := fun (j : ℕ) (hj : j<N+(R.card-1)) (x : Fin n → Bool) =>
    splice_value V hR hRb hp (Nat.le_of_lt hh) hAb hab haliasb halias hval hpatch (j := j) hj x
  have hOut : embed n h (R.card-1) out<n+(N+(R.card-1)) := embed_back (by omega) hout
  obtain ⟨E,hEAO,hEsize,hEval⟩ := AliasCompiler.compile_circuit n (expanded V h R)
    (spliceOp h R A op) (fun j=>some (link j)) (spliceA n h p R a) (spliceB n h R b)
    hInput (N+(R.card-1)) hAlias hBack hValue (embed n h (R.card-1) out) hOut
  have hAsub : A⊆Finset.range (N+(R.card-1)) := by
    intro j hj
    have := hAb j hj
    exact Finset.mem_range.mpr (by omega)
  have hsub : (Finset.range (N+(R.card-1))).filter (fun j=>spliceOp h R A op j≠none)⊆
      (Finset.range (N+(R.card-1)))\A := by
    intro j hj
    obtain ⟨hjr,hjn⟩ := Finset.mem_filter.mp hj
    refine Finset.mem_sdiff.mpr ⟨hjr,?_⟩
    intro hjA
    exact hjn (by simp [spliceOp,hjA])
  have hCard := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hAsub,Finset.card_range] at hCard
  have hr := Finset.card_pos.mpr hR
  refine ⟨E,hEAO,by omega,?_⟩
  intro x
  exact (hEval x).trans (expanded_embed V h R out x)

end SpliceAlias

namespace MultiMixedProjection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.H5Support PEqualNP.Outside.L_meta_5012.H5Support.Mixed
  PEqualNP.Outside.L_meta_5012.SemiMixedSingleton

lemma true_wire_bound {n : ℕ} {C : Circuit} {x : Fin n → Bool} {w : ℕ}
    (hx : W n C x w=true) : w<n+C.gates.length := by
  by_contra hh
  have hl := wires_length n C x
  have hf : W n C x w=false := getD_ge_length _ w (by omega)
  rw [hf] at hx
  contradiction

lemma preserve_frontier {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (J : Finset ℕ) (U : ℕ → (Fin n → Bool) → Bool)
    (hin : ∀v : Fin n,∀x,U v.val x=x v)
    (hor : ∀k,k<C.gates.length → k∉J → (gateAt C k).op=GateOp.or → ∀x,
      U (n+k) x=(U (opnd C k 0) x || U (opnd C k 1) x))
    (x : Fin n → Bool) :
    ∀w, (∀k,k<C.gates.length → OrReaches n C w k → (gateAt C k).op=GateOp.and →
      gateVal n C k x=true → U (n+k) x=true) →
      (∀k∈J,OrReaches n C w k → gateVal n C k x=true → U (n+k) x=true) →
      W n C x w=true → U w x=true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hA hJ hx
    by_cases hwn : w<n
    · rw [W_input n C x w hwn] at hx
      exact (hin ⟨w,hwn⟩ x).trans hx
    have hw := true_wire_bound hx
    have hk : w-n<C.gates.length := by omega
    have he : n+(w-n)=w := by omega
    have hself : OrReaches n C w (w-n) := by
      simpa only [he] using orReach_self n C (w-n) hk
    have hxk : gateVal n C (w-n) x=true := by
      change W n C x (n+(w-n))=true
      simpa only [he] using hx
    rcases hAO.1 _ (gateAt_mem' C (w-n) hk) with hand | horig
    · simpa only [he] using hA (w-n) hk hself hand hxk
    by_cases hkJ : w-n∈J
    · simpa only [he] using hJ (w-n) hkJ hself hxk
    have hold := or_two_value hAO hk horig x
    rw [hxk] at hold
    have hold' : wireVal n C (opnd C (w-n) 0) x=true ∨
        wireVal n C (opnd C (w-n) 1) x=true := by
      simpa only [Bool.or_eq_true] using hold.symm
    obtain ⟨b,hb⟩ : ∃b : Fin 2,W n C x (opnd C (w-n) b)=true := by
      rcases hold' with hh | hh
      · exact ⟨0,hh⟩
      · exact ⟨1,hh⟩
    have hbback := opnd_lt hAO hk b
    have hsub (j : ℕ) (hr : OrReaches n C (opnd C (w-n) b) j) : OrReaches n C w j := by
      rw [←he]
      exact orReach_trans n C (w-n) hk horig _ (opnd_mem hAO hk b) hbback j hr
    have hnew := ih (opnd C (w-n) b) (by omega)
      (fun j hj hr hop hv => hA j hj (hsub j hr) hop hv)
      (fun j hj hr hv => hJ j hj (hsub j hr) hv) hb
    rw [←he,hor (w-n) hk hkJ horig]
    simp only [Bool.or_eq_true]
    fin_cases b
    · exact Or.inl hnew
    · exact Or.inr hnew

lemma pure_raw_wire_preserves {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (J : Finset ℕ) (U : ℕ → (Fin n → Bool) → Bool)
    (hin : ∀v : Fin n,∀x,U v.val x=x v)
    (hor : ∀k,k<C.gates.length → k∉J → (gateAt C k).op=GateOp.or → ∀x,
      U (n+k) x=(U (opnd C k 0) x || U (opnd C k 1) x))
    (s : Fin n → Bool) (hmix : ∀e∈J,∀c : Bool,gateVal n C e (monoInput s c)=true)
    (w : ℕ) (S : Finset (Fin n)) (c : Bool)
    (hsem : ∀x,wireVal n C w x=decide (∃v∈S,x v=true))
    (hcolor : ∀v∈S,s v=c)
    (hraw : ∀k,k<C.gates.length → OrReaches n C w k → (gateAt C k).op=GateOp.or)
    (x : Fin n → Bool) (hx : W n C x w=true) : U w x=true := by
  apply preserve_frontier hAO J U hin hor x w _ _ hx
  · intro k hk hr hand _
    rw [hraw k hk hr] at hand
    contradiction
  · intro e heJ hr _
    have hbad := reach_up n C (monoInput s (!c)) w e hr (hmix e heJ (!c))
    change wireVal n C w (monoInput s (!c))=true at hbad
    rw [hsem] at hbad
    obtain ⟨v,hv,hvc⟩ := of_decide_eq_true hbad
    have he : c= !c := (hcolor v hv).symm.trans (of_decide_eq_true hvc)
    cases c <;> cases he

lemma projected_gate_true_of_clean_filter {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (s : Fin n → Bool)
    (hcol : ∀a b,G.Adj a b → s a≠s b)
    (g e : ℕ) (v : Fin n) (hv : s v=true)
    (hcenter : ∀x,gateVal n C g x=true → x v=true)
    (hdirty : ∃x,gateVal n C g x=true ∧ graphFun G ∅ x=false)
    (hraw : ∀x,gateVal n C e x=decide (∃q∈orIn n C (n+e),x q=true))
    (hfilter : ∀x,gateVal n C e x=true → gateVal n C g x=true → graphFun G ∅ x=true)
    (U : ℕ → (Fin n → Bool) → Bool)
    (hlift : ∀q∈orIn n C (n+e),s q=false → ∀x,x q=true → U (n+e) x=true)
    (a b : Fin n) (hab : G.Adj a b)
    (hg : gateVal n C g (pairInput a b)=true) (he : gateVal n C e (pairInput a b)=true) :
    U (n+e) (pairInput a b)=true := by
  have hvnot : v∉orIn n C (n+e) := by
    intro hvmem
    obtain ⟨x,hgx,hFx⟩ := hdirty
    have hex : gateVal n C e x=true := orIn_val n C x (n+e) v hvmem (hcenter x hgx)
    have hf := hfilter x hex hgx
    rw [hFx] at hf
    contradiction
  rw [hraw] at he
  obtain ⟨q,hq,hxq⟩ := of_decide_eq_true he
  have hqcolor : s q=false := by
    cases hqc : s q with
    | false => rfl
    | true =>
      have heq : q=v := pair_same_color_eq hcol hab (hcenter _ hg) hxq (hqc.trans hv.symm)
      subst q
      exact False.elim (hvnot hq)
  exact hlift q hq hqcolor _ hxq

lemma clean_and_preserves_graph_pair {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C) (hTop : TopForm G C)
    (s : Fin n → Bool) (hcol : ∀a b,G.Adj a b → s a≠s b)
    (g h : ℕ) (hJunk : junk G C={g,h})
    (hmono : gateVal n C h (monoInput s false)=true)
    (v : Fin n) (hv : s v=true) (hcenter : ∀x,gateVal n C g x=true → x v=true)
    (J : Finset ℕ) (U : ℕ → (Fin n → Bool) → Bool)
    (hin : ∀v : Fin n,∀x,U v.val x=x v)
    (hor : ∀k,k<C.gates.length → k∉J → (gateAt C k).op=GateOp.or → ∀x,
      U (n+k) x=(U (opnd C k 0) x || U (opnd C k 1) x))
    (hand : ∀k,k<C.gates.length → (gateAt C k).op=GateOp.and → BelowF G C k → ∀x,
      U (n+k) x=(U (opnd C k 0) x && U (opnd C k 1) x))
    (hmix : ∀e∈J,∀c : Bool,gateVal n C e (monoInput s c)=true)
    (hraw : ∀e∈J,∀x,gateVal n C e x=decide (∃q∈orIn n C (n+e),x q=true))
    (hlift : ∀e∈J,∀q∈orIn n C (n+e),s q=false → ∀x,x q=true → U (n+e) x=true)
    (a b : Fin n) (hab : G.Adj a b)
    (hpres : ∀k∈junk G C,gateVal n C k (pairInput a b)=true → U (n+k) (pairInput a b)=true)
    (t : ℕ) (ht : t<C.gates.length) (htand : (gateAt C t).op=GateOp.and)
    (htbelow : BelowF G C t) (htx : gateVal n C t (pairInput a b)=true) :
    U (n+t) (pairInput a b)=true := by
  let x := pairInput a b
  have hgJ : g∈junk G C := by simp [hJunk]
  obtain ⟨_,_,_,xg,hgx,hgFx⟩ := mem_junk.mp hgJ
  have hoperand (i : Fin 2) : U (opnd C t i) x=true := by
    apply preserve_frontier hAO J U hin hor x (opnd C t i)
    · intro k hk hr hkand hkx
      have hcone := reach_cone n C t ht _ (opnd_mem hAO ht i) (opnd_lt hAO ht i) k hr
      exact hpres k (and_ancestor_junk hTop ht htand hk hkand hcone) hkx
    · intro e heJ hr hex
      obtain ⟨_,_,hrg,heq⟩ := opposite_of_semimixed_gate G C s hcol hAO hTop g h hJunk
        hmono e (hmix e heJ) t ht htand htbelow i hr
      have hgt : gateVal n C g x=true := by
        have ho := and_true_operands hAO ht htand x htx (1-i)
        change wireVal n C (opnd C t (1-i)) x=true at ho
        rwa [heq] at ho
      have hfilter (y : Fin n → Bool) (hey : gateVal n C e y=true) (hgy : gateVal n C g y=true) :
          graphFun G ∅ y=true :=
        htbelow y (and_two hAO ht htand i y
          (reach_up n C y _ e hr hey) (reach_up n C y _ g hrg hgy))
      exact projected_gate_true_of_clean_filter s hcol g e v hv hcenter ⟨xg,hgx,hgFx⟩
        (hraw e heJ) hfilter U (hlift e heJ) a b hab hgt hex
    · exact and_true_operands hAO ht htand x htx i
  rw [hand t ht htand htbelow]
  change (U (opnd C t 0) x && U (opnd C t 1) x)=true
  rw [hoperand 0,hoperand 1]
  rfl

lemma output_preserves_graph_pairs {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C) (hTop : TopForm G C)
    (hF : circuitFun n C=graphFun G ∅)
    (s : Fin n → Bool) (hcol : ∀a b,G.Adj a b → s a≠s b)
    (g h : ℕ) (hJunk : junk G C={g,h})
    (hmono : gateVal n C h (monoInput s false)=true)
    (v : Fin n) (hv : s v=true) (hcenter : ∀x,gateVal n C g x=true → x v=true)
    (J : Finset ℕ) (U : ℕ → (Fin n → Bool) → Bool)
    (hin : ∀v : Fin n,∀x,U v.val x=x v)
    (hor : ∀k,k<C.gates.length → k∉J → (gateAt C k).op=GateOp.or → ∀x,
      U (n+k) x=(U (opnd C k 0) x || U (opnd C k 1) x))
    (hand : ∀k,k<C.gates.length → (gateAt C k).op=GateOp.and → BelowF G C k → ∀x,
      U (n+k) x=(U (opnd C k 0) x && U (opnd C k 1) x))
    (hmix : ∀e∈J,∀c : Bool,gateVal n C e (monoInput s c)=true)
    (hraw : ∀e∈J,∀x,gateVal n C e x=decide (∃q∈orIn n C (n+e),x q=true))
    (hlift : ∀e∈J,∀q∈orIn n C (n+e),s q=false → ∀x,x q=true → U (n+e) x=true)
    (hpres : ∀k∈junk G C,∀a b,G.Adj a b →
      gateVal n C k (pairInput a b)=true → U (n+k) (pairInput a b)=true) :
    ∀a b,G.Adj a b → U C.output (pairInput a b)=true := by
  intro a b hab
  apply preserve_frontier hAO J U hin hor (pairInput a b) C.output
  · intro k hk hr hkand hkx
    rcases and_junk_or_below (G := G) hk hkand with hkJ | hkbelow
    · exact hpres k hkJ a b hab hkx
    · exact clean_and_preserves_graph_pair hAO hTop s hcol g h hJunk hmono v hv hcenter
        J U hin hor hand hmix hraw hlift a b hab (fun j hj => hpres j hj a b hab)
        k hk hkand hkbelow hkx
  · intro e heJ hr _
    exact False.elim (output_not_reaches_mixed hcol hF (hmix e heJ) hr)
  · change circuitFun n C (pairInput a b)=true
    rw [hF]
    exact (graph_true G (pairInput a b)).mpr ⟨a,b,hab,by simp [pairInput],by simp [pairInput]⟩

lemma output_computes_of_pairs_under_mono {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hF : circuitFun n C=graphFun G ∅)
    (U : ℕ → (Fin n → Bool) → Bool)
    (hpairs : ∀a b,G.Adj a b → U C.output (pairInput a b)=true)
    (hunder : ∀x,U C.output x=true → W n C x C.output=true)
    (hmono : ∀x y,(∀v,x v=true → y v=true) → U C.output x=true → U C.output y=true) :
    U C.output=graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    have ho := hunder x hx
    change circuitFun n C x=true at ho
    rwa [hF] at ho
  · intro hx
    obtain ⟨a,b,hab,ha,hb⟩ := (graph_true G x).mp hx
    apply hmono (pairInput a b) x _ (hpairs a b hab)
    intro v hv
    have he : v=a ∨ v=b := of_decide_eq_true hv
    rcases he with rfl | rfl
    · exact ha
    · exact hb

lemma compiled_computes_of_pairs_under {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hF : circuitFun n C=graphFun G ∅)
    (U : ℕ → (Fin n → Bool) → Bool)
    (hpairs : ∀a b,G.Adj a b → U C.output (pairInput a b)=true)
    (hunder : ∀x,U C.output x=true → W n C x C.output=true)
    (E : Circuit) (hEAO : IsAO2 n E)
    (hEval : ∀x,circuitFun n E x=U C.output x) : circuitFun n E=graphFun G ∅ := by
  have hmono : ∀x y,(∀v,x v=true → y v=true) → U C.output x=true → U C.output y=true := by
    intro x y hxy hx
    rw [←hEval] at hx ⊢
    exact circuit_mono (ao_mono hEAO) hxy hx
  have hU := output_computes_of_pairs_under_mono hF U hpairs hunder hmono
  funext x
  rw [hEval,hU]

lemma no_least_compiled_projection {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hL : IsLeastAO G C)
    (U : ℕ → (Fin n → Bool) → Bool)
    (hpairs : ∀a b,G.Adj a b → U C.output (pairInput a b)=true)
    (hunder : ∀x,U C.output x=true → W n C x C.output=true)
    (E : Circuit) (hEAO : IsAO2 n E) (hsize : E.size<C.size)
    (hEval : ∀x,circuitFun n E x=U C.output x) : False := by
  have hF := compiled_computes_of_pairs_under hL.2.1 U hpairs hunder E hEAO hEval
  have hmin := hL.2.2 E hEAO hF
  omega

lemma semimixed_pair_right_witness {n : ℕ} {G : SimpleGraph (Fin n)}
    (s : Fin n → Bool) (hcol : ∀a b,G.Adj a b → s a≠s b)
    (A B : Finset (Fin n)) (hA : ∀v∈A,s v=false) (hdis : Disjoint A B)
    (a b : Fin n) (hab : G.Adj a b)
    (hpa : decide (∃v∈A,pairInput a b v=true)=true)
    (hpb : decide (∃v∈B,pairInput a b v=true)=true) :
    ∃v∈B,s v=true ∧ pairInput a b v=true := by
  obtain ⟨u,hu,hpu⟩ := of_decide_eq_true hpa
  obtain ⟨v,hv,hpv⟩ := of_decide_eq_true hpb
  refine ⟨v,hv,?_,hpv⟩
  cases hvc : s v with
  | true => rfl
  | false =>
    have he : v=u := pair_same_color_eq hcol hab hpu hpv (hvc.trans (hA u hu).symm)
    subst v
    exact False.elim (Finset.disjoint_left.mp hdis hu hv)

lemma h_pair_preserved_of_right_cover {n : ℕ} {G : SimpleGraph (Fin n)}
    {C : Circuit} (s : Fin n → Bool) (hcol : ∀a b,G.Adj a b → s a≠s b)
    (h p : ℕ) (A B : Finset (Fin n)) (R : Finset ℕ) (S : ℕ → Finset (Fin n))
    (U : ℕ → (Fin n → Bool) → Bool)
    (hA : ∀v∈A,s v=false) (hdis : Disjoint A B)
    (hcover : B.filter (fun v => s v=true)=R.biUnion S)
    (hold : ∀x,gateVal n C h x=
      (decide (∃v∈A,x v=true) && decide (∃v∈B,x v=true)))
    (hpU : ∀x,decide (∃v∈A,x v=true)=true → U p x=true)
    (hRU : ∀r∈R,∀x,decide (∃v∈S r,x v=true)=true → U r x=true)
    (hnew : ∀x,U (n+h) x=(U p x && decide (∃r∈R,U r x=true))) :
    ∀a b,G.Adj a b → gateVal n C h (pairInput a b)=true → U (n+h) (pairInput a b)=true := by
  intro a b hab hhold
  rw [hold] at hhold
  have hh : decide (∃v∈A,pairInput a b v=true)=true ∧
      decide (∃v∈B,pairInput a b v=true)=true := by
    simpa only [Bool.and_eq_true] using hhold
  obtain ⟨v,hv,hvc,hpv⟩ := semimixed_pair_right_witness s hcol A B hA hdis a b hab hh.1 hh.2
  have hvm : v∈R.biUnion S := by rw [←hcover]; exact Finset.mem_filter.mpr ⟨hv,hvc⟩
  obtain ⟨r,hr,hvr⟩ := Finset.mem_biUnion.mp hvm
  have hrU : U r (pairInput a b)=true := hRU r hr _ (decide_eq_true ⟨v,hvr,hpv⟩)
  rw [hnew,hpU _ hh.1,Bool.true_and]
  exact decide_eq_true ⟨r,hr,hrU⟩

lemma binary_source_preserves {n : ℕ} {C : Circuit}
    (U : ℕ → (Fin n → Bool) → Bool) (g p q : ℕ)
    (hold : ∀x,gateVal n C g x=(wireVal n C p x && wireVal n C q x))
    (hnew : ∀x,U (n+g) x=(U p x && U q x))
    (hp : ∀x,wireVal n C p x=true → U p x=true)
    (hq : ∀x,wireVal n C q x=true → U q x=true) :
    ∀x,gateVal n C g x=true → U (n+g) x=true := by
  intro x hx
  rw [hold] at hx
  have hh : wireVal n C p x=true ∧ wireVal n C q x=true := by
    simpa only [Bool.and_eq_true] using hx
  rw [hnew,hp x hh.1,hq x hh.2]
  rfl

end MultiMixedProjection

namespace LeftProjectionPreservation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_5012.H5Support PEqualNP.Outside.L_meta_5012.H5Support.Mixed
open MultiMixedProjection

lemma pure_value_preserves {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (J : Finset ℕ) (I : Finset (Fin n)) (h p : ℕ) (R : Finset ℕ)
    (hhop : (gateAt C h).op=GateOp.and)
    (s : Fin n → Bool) (hmix : ∀e∈J,∀c : Bool,gateVal n C e (monoInput s c)=true)
    (w : ℕ) (c : Bool) (hcolor : ∀v∈orIn n C w,s v=c)
    (hraw : ∀k,k<C.gates.length → OrReaches n C w k → (gateAt C k).op=GateOp.or)
    (x : Fin n → Bool) (hx : W n C x w=true) :
    LeftProjectionEval.value C J (orIn n C) I h p R x w=true := by
  let U : ℕ → (Fin n → Bool) → Bool := fun w x => LeftProjectionEval.value C J (orIn n C) I h p R x w
  have hin (v : Fin n) (x : Fin n → Bool) : U v.val x=x v :=
    LeftProjectionEval.input C J (orIn n C) I h p R x v.val v.isLt
  have hor (k : ℕ) (hk : k<C.gates.length) (hkJ : k∉J) (hop : (gateAt C k).op=GateOp.or)
      (x : Fin n → Bool) : U (n+k) x=(U (opnd C k 0) x || U (opnd C k 1) x) := by
    have hkh : k≠h := by intro he; subst k; rw [hhop] at hop; contradiction
    dsimp only [U]
    rw [LeftProjectionEval.ordinary hAO J (orIn n C) I h p R x k hk hkJ hkh,
      hop,Frontier.gate_inputs_eq hAO hk]
    simp only [List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,Bool.or_false,id_eq]
  have hsem (x : Fin n → Bool) : wireVal n C w x=decide (∃v∈orIn n C w,x v=true) :=
    SingletonPrivacy.W_eq_setOr_of_raw hAO w hraw x
  exact pure_raw_wire_preserves hAO J U hin hor s hmix w (orIn n C w) c hsem hcolor hraw x hx

lemma junk_pairs_preserved {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C)
    (s : Fin n → Bool) (hcol : ∀a b,G.Adj a b → s a≠s b)
    (g h p q : ℕ) (hgh : g≠h) (hJunk : junk G C={g,h})
    (hhin : (gateAt C h).inputs=[p,q] ∨ (gateAt C h).inputs=[q,p])
    (J : Finset ℕ) (I : Finset (Fin n)) (R : Finset ℕ)
    (hJOR : ∀e∈J,(gateAt C e).op=GateOp.or)
    (hmix : ∀e∈J,∀c : Bool,gateVal n C e (monoInput s c)=true)
    (hgColors : ∀b : Fin 2,∃c : Bool,∀v∈side (n := n) C g b,s v=c)
    (hgRaw : ∀b : Fin 2,∀k,k<C.gates.length → OrReaches n C (opnd C g b) k →
      (gateAt C k).op=GateOp.or)
    (hpColor : ∀v∈orIn n C p,s v=false)
    (hpRaw : ∀k,k<C.gates.length → OrReaches n C p k → (gateAt C k).op=GateOp.or)
    (hqRaw : ∀k,k<C.gates.length → OrReaches n C q k → (gateAt C k).op=GateOp.or)
    (hDis : Disjoint (orIn n C p) (orIn n C q))
    (hRbound : ∀r∈R,r<n+h)
    (hRcolor : ∀r∈R,∀v∈orIn n C r,s v=true)
    (hRraw : ∀r∈R,∀k,k<C.gates.length → OrReaches n C r k → (gateAt C k).op=GateOp.or)
    (hCover : (orIn n C q).filter (fun v => s v=true)=R.biUnion (orIn n C)) :
    ∀k∈junk G C,∀a b,G.Adj a b → gateVal n C k (pairInput a b)=true →
      LeftProjectionEval.value C J (orIn n C) I h p R (pairInput a b) (n+k)=true := by
  have hgJ : g∈junk G C := by simp [hJunk]
  have hhJ : h∈junk G C := by simp [hJunk]
  obtain ⟨hglen,hgand,_⟩ := mem_junk.mp hgJ
  obtain ⟨hhlen,hhand,_⟩ := mem_junk.mp hhJ
  have hgnot : g∉J := by intro hh; have ho := hJOR g hh; rw [hgand] at ho; contradiction
  have hhnot : h∉J := by intro hh; have ho := hJOR h hh; rw [hhand] at ho; contradiction
  have hpback : p<n+h := hAO.2.1 h hhlen p (by rcases hhin with hh | hh <;> simp [hh])
  let U : ℕ → (Fin n → Bool) → Bool := fun w x => LeftProjectionEval.value C J (orIn n C) I h p R x w
  have gpres : ∀x,gateVal n C g x=true → U (n+g) x=true := by
    apply binary_source_preserves U g (opnd C g 0) (opnd C g 1)
    · intro x
      change Frontier.W n C x (n+g)=_
      rw [RootPatch.W_gate_eq hAO x hglen,hgand,Frontier.gate_inputs_eq hAO hglen]
      simp only [List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,Bool.and_true,id_eq]
      rfl
    · intro x
      dsimp only [U]
      rw [LeftProjectionEval.ordinary hAO J (orIn n C) I h p R x g hglen hgnot hgh,
        hgand,Frontier.gate_inputs_eq hAO hglen]
      simp only [List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,Bool.and_true,id_eq]
    · intro x hx
      obtain ⟨c,hc⟩ := hgColors 0
      exact pure_value_preserves hAO J I h p R hhand s hmix _ c hc (hgRaw 0) x hx
    · intro x hx
      obtain ⟨c,hc⟩ := hgColors 1
      exact pure_value_preserves hAO J I h p R hhand s hmix _ c hc (hgRaw 1) x hx
  have hpres : ∀a b,G.Adj a b → gateVal n C h (pairInput a b)=true → U (n+h) (pairInput a b)=true := by
    apply h_pair_preserved_of_right_cover s hcol h p (orIn n C p) (orIn n C q) R (orIn n C)
      U hpColor hDis hCover
    · intro x
      have hpsem := SingletonPrivacy.W_eq_setOr_of_raw hAO p hpRaw x
      have hqsem := SingletonPrivacy.W_eq_setOr_of_raw hAO q hqRaw x
      change Frontier.W n C x (n+h)=_
      rw [RootPatch.W_gate_eq hAO x hhlen,hhand]
      rcases hhin with hi | hi <;> rw [hi] <;> simp only [List.map_cons,List.map_nil,GateOp.eval,
        List.all_cons,List.all_nil,Bool.and_true,id_eq,hpsem,hqsem]
      · rfl
      · exact Bool.and_comm _ _
    · intro x hx
      apply pure_value_preserves hAO J I h p R hhand s hmix p false hpColor hpRaw x
      change Frontier.W n C x p=true
      rw [SingletonPrivacy.W_eq_setOr_of_raw hAO p hpRaw x]
      exact hx
    · intro r hr x hx
      apply pure_value_preserves hAO J I h p R hhand s hmix r true (hRcolor r hr) (hRraw r hr) x
      change Frontier.W n C x r=true
      rw [SingletonPrivacy.W_eq_setOr_of_raw hAO r (hRraw r hr) x]
      exact hx
    · intro x
      exact LeftProjectionEval.special C J (orIn n C) I h p R x hhlen hhnot hpback hRbound
  intro k hk a b hab hkx
  have hk' : k=g ∨ k=h := by simpa [hJunk] using hk
  rcases hk' with rfl | rfl
  · exact gpres _ hkx
  · exact hpres a b hab hkx

end LeftProjectionPreservation

namespace CanonicalMixed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open Frontier SingletonPrivacy

def leftSet {n : ℕ} (s : Fin n → Bool) : Finset (Fin n) := Finset.univ.filter (fun v=>s v=false)
def rightSet {n : ℕ} (s : Fin n → Bool) : Finset (Fin n) := Finset.univ.filter (fun v=>s v=true)

noncomputable def J (n : ℕ) (C : Circuit) (s : Fin n → Bool) (r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun j=>OrReaches n C (n+r) j ∧
    (orIn n C (n+j)∩leftSet s).Nonempty ∧ (orIn n C (n+j)∩rightSet s).Nonempty

noncomputable def R (n : ℕ) (C : Circuit) (s : Fin n → Bool) (r : ℕ) : Finset ℕ := by
  classical
  exact (J n C s r).biUnion fun j=>(gateAt C j).inputs.toFinset.filter
    (fun w=>orIn n C w⊆rightSet s)

lemma mem_J {n : ℕ} {C : Circuit} {s : Fin n → Bool} {r j : ℕ} :
    j∈J n C s r ↔ j<C.gates.length ∧ OrReaches n C (n+r) j ∧
      (orIn n C (n+j)∩leftSet s).Nonempty ∧ (orIn n C (n+j)∩rightSet s).Nonempty := by
  classical
  simp [J]

lemma mem_R {n : ℕ} {C : Circuit} {s : Fin n → Bool} {r w : ℕ} :
    w∈R n C s r ↔ ∃j∈J n C s r,w∈(gateAt C j).inputs ∧ orIn n C w⊆rightSet s := by
  classical
  simp [R]

lemma colors_disjoint {n : ℕ} (s : Fin n → Bool) : Disjoint (leftSet s) (rightSet s) := by
  apply Finset.disjoint_left.mpr
  intro v hv ht
  simp only [leftSet,rightSet,Finset.mem_filter,Finset.mem_univ,true_and] at hv ht
  rw [hv] at ht
  contradiction

lemma pure_of_not_mixed {n : ℕ} (s : Fin n → Bool) (S : Finset (Fin n))
    (hnot : ¬((S∩leftSet s).Nonempty ∧ (S∩rightSet s).Nonempty)) :
    S⊆leftSet s ∨ S⊆rightSet s := by
  by_cases hL : (S∩leftSet s).Nonempty
  · left
    intro v hv
    by_cases hs : s v=false
    · simp [leftSet,hs]
    · have ht : s v=true := by cases he:s v <;> simp_all
      exact False.elim (hnot ⟨hL,⟨v,Finset.mem_inter.mpr ⟨hv,by simp [rightSet,ht]⟩⟩⟩)
  · right
    intro v hv
    by_cases hs : s v=true
    · simp [rightSet,hs]
    · have ht : s v=false := by cases he:s v <;> simp_all
      exact False.elim (hL ⟨v,Finset.mem_inter.mpr ⟨hv,by simp [leftSet,ht]⟩⟩)

lemma root_mem {n : ℕ} {C : Circuit} {s : Fin n → Bool} {r : ℕ}
    (hr : r<C.gates.length)
    (hL : (orIn n C (n+r)∩leftSet s).Nonempty)
    (hR : (orIn n C (n+r)∩rightSet s).Nonempty) : r∈J n C s r :=
  mem_J.mpr ⟨hr,orReach_self n C r hr,hL,hR⟩

lemma region_before {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {s : Fin n → Bool} {r h : ℕ}
    (hh : h<C.gates.length) (hroot : n+r∈(gateAt C h).inputs) : ∀j∈J n C s r,j<h := by
  intro j hj
  exact inCone_lt n C h j (reach_cone n C h hh (n+r) hroot (hAO.2.1 h hh _ hroot) j
    (mem_J.mp hj).2.1)

lemma region_or {n : ℕ} {C : Circuit} {s : Fin n → Bool} {r : ℕ}
    (hraw : ∀k,k<C.gates.length→OrReaches n C (n+r) k→(gateAt C k).op=GateOp.or) :
    ∀j∈J n C s r,(gateAt C j).op=GateOp.or := by
  intro j hj
  exact hraw j (mem_J.mp hj).1 (mem_J.mp hj).2.1

lemma child_reaches_root {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {s : Fin n → Bool} {r j w k : ℕ}
    (hr : r<C.gates.length)
    (hraw : ∀k,k<C.gates.length→OrReaches n C (n+r) k→(gateAt C k).op=GateOp.or)
    (hj : j∈J n C s r) (hw : w∈(gateAt C j).inputs) (hk : OrReaches n C w k) :
    OrReaches n C (n+r) k := by
  have hd := mem_J.mp hj
  exact orReach_comp hr hd.2.1
    (orReach_trans n C j hd.1 (hraw j hd.1 hd.2.1) w hw (hAO.2.1 j hd.1 w hw) k hk)

lemma child_raw {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {s : Fin n → Bool} {r j w : ℕ}
    (hr : r<C.gates.length)
    (hraw : ∀k,k<C.gates.length→OrReaches n C (n+r) k→(gateAt C k).op=GateOp.or)
    (hj : j∈J n C s r) (hw : w∈(gateAt C j).inputs) :
    ∀k,k<C.gates.length→OrReaches n C w k→(gateAt C k).op=GateOp.or := by
  intro k hk hkw
  exact hraw k hk (child_reaches_root hAO hr hraw hj hw hkw)

lemma child_value {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {s : Fin n → Bool} {r j w : ℕ}
    (hr : r<C.gates.length)
    (hraw : ∀k,k<C.gates.length→OrReaches n C (n+r) k→(gateAt C k).op=GateOp.or)
    (hj : j∈J n C s r) (hw : w∈(gateAt C j).inputs) (x : Fin n → Bool) :
    W n C x w=setOr (orIn n C w) x :=
  W_eq_setOr_of_raw hAO w (child_raw hAO hr hraw hj hw) x

lemma child_support_subset {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {s : Fin n → Bool} {r j w : ℕ} (hr : r<C.gates.length)
    (hraw : ∀k,k<C.gates.length→OrReaches n C (n+r) k→(gateAt C k).op=GateOp.or)
    (hj : j∈J n C s r) (hw : w∈(gateAt C j).inputs) :
    orIn n C w⊆orIn n C (n+r) := by
  intro v hv
  rcases (orIn_mem n C w v).mp hv with he | ⟨k,hk,hreach,hop,hin⟩
  · exact (orIn_mem n C (n+r) v).mpr (Or.inr
      ⟨j,(mem_J.mp hj).1,(mem_J.mp hj).2.1,region_or hraw j hj,he ▸ hw⟩)
  · exact (orIn_mem n C (n+r) v).mpr (Or.inr
      ⟨k,hk,child_reaches_root hAO hr hraw hj hw hreach,hop,hin⟩)

lemma child_positive_root {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {s : Fin n → Bool} {r j w : ℕ}
    (hraw : ∀k,k<C.gates.length→OrReaches n C (n+r) k→(gateAt C k).op=GateOp.or)
    (hj : j∈J n C s r) (hw : w∈(gateAt C j).inputs) (x : Fin n → Bool) :
    W n C x w=true→W n C x (n+r)=true := by
  intro hx
  have hd := mem_J.mp hj
  exact reach_up n C x (n+r) j hd.2.1
    (W_or n C x j hd.1 (region_or hraw j hj) w hw (hAO.2.1 j hd.1 w hw) hx)

lemma region_value {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {s : Fin n → Bool} {r : ℕ}
    (hr : r<C.gates.length)
    (hraw : ∀k,k<C.gates.length→OrReaches n C (n+r) k→(gateAt C k).op=GateOp.or) :
    ∀j∈J n C s r,∀x,W n C x (n+j)=setOr (orIn n C (n+j)) x := by
  intro j hj x
  exact root_descendant_value hAO hr hraw (mem_J.mp hj).2.1 x

lemma region_union {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {s : Fin n → Bool} {r : ℕ}
    (hr : r<C.gates.length)
    (hraw : ∀k,k<C.gates.length→OrReaches n C (n+r) k→(gateAt C k).op=GateOp.or) :
    ∀j∈J n C s r,orIn n C (n+j)=orIn n C (opnd C j 0)∪orIn n C (opnd C j 1) := by
  intro j hj
  have hjN := (mem_J.mp hj).1
  have hin (b : Fin 2) : opnd C j b∈(gateAt C j).inputs := by
    rw [gate_inputs_eq hAO hjN]
    fin_cases b <;> simp
  have he (x : Fin n → Bool) : setOr (orIn n C (n+j)) x=
      (setOr (orIn n C (opnd C j 0)) x||setOr (orIn n C (opnd C j 1)) x) := by
    rw [←region_value hAO hr hraw j hj x,RootPatch.W_gate_eq hAO x hjN,
      region_or hraw j hj,gate_inputs_eq hAO hjN]
    simp only [List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,Bool.or_false,id_eq]
    rw [child_value hAO hr hraw hj (hin 0) x,child_value hAO hr hraw hj (hin 1) x]
  ext v
  have hv := congrArg (fun b:Bool=>b=true) (he (pairInput v v))
  simp only [Bool.or_eq_true,setOr_pair,or_self] at hv
  exact (eq_iff_iff.mp hv).trans Finset.mem_union.symm

lemma mixed_child_internal {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {s : Fin n → Bool} {r j w : ℕ} (hr : r<C.gates.length)
    (hraw : ∀k,k<C.gates.length→OrReaches n C (n+r) k→(gateAt C k).op=GateOp.or)
    (hj : j∈J n C s r) (hw : w∈(gateAt C j).inputs)
    (hL : (orIn n C w∩leftSet s).Nonempty)
    (hR : (orIn n C w∩rightSet s).Nonempty) : n≤w ∧ w-n∈J n C s r := by
  have hwn : n≤w := by
    by_contra hn
    have hlt : w<n := by omega
    have hs := orIn_raw_singleton C (⟨w,hlt⟩:Fin n)
    obtain ⟨v,hv⟩ := hL
    obtain ⟨hvS,hvL⟩ := Finset.mem_inter.mp hv
    obtain ⟨z,hz⟩ := hR
    obtain ⟨hzS,hzR⟩ := Finset.mem_inter.mp hz
    rw [hs] at hvS hzS
    have hvz : v=z := (Finset.mem_singleton.mp hvS).trans (Finset.mem_singleton.mp hzS).symm
    exact Finset.disjoint_left.mp (colors_disjoint s) hvL (hvz.symm ▸ hzR)
  have hd := input_reaches_root hAO hr (mem_J.mp hj).1 (mem_J.mp hj).2.1 (region_or hraw j hj) hw hwn
  have he : n+(w-n)=w := by omega
  exact ⟨hwn,mem_J.mpr ⟨hd.1,hd.2,by simpa only [he] using hL,by simpa only [he] using hR⟩⟩

lemma outside_child_pure {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {s : Fin n → Bool} {r j w : ℕ} (hr : r<C.gates.length)
    (hraw : ∀k,k<C.gates.length→OrReaches n C (n+r) k→(gateAt C k).op=GateOp.or)
    (hj : j∈J n C s r) (hw : w∈(gateAt C j).inputs)
    (hout : ¬(n≤w ∧ w-n∈J n C s r)) : orIn n C w⊆leftSet s ∨ orIn n C w⊆rightSet s := by
  apply pure_of_not_mixed s
  rintro ⟨hL,hR⟩
  exact hout (mixed_child_internal hAO hr hraw hj hw hL hR)

lemma outside_not_right_left {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {s : Fin n → Bool} {r j w : ℕ} (hr : r<C.gates.length)
    (hraw : ∀k,k<C.gates.length→OrReaches n C (n+r) k→(gateAt C k).op=GateOp.or)
    (hj : j∈J n C s r) (hw : w∈(gateAt C j).inputs)
    (hout : ¬(n≤w ∧ w-n∈J n C s r)) (hnot : w∉R n C s r) : orIn n C w⊆leftSet s := by
  rcases outside_child_pure hAO hr hraw hj hw hout with hL | hR
  · exact hL
  · exact False.elim (hnot (mem_R.mpr ⟨j,hj,hw,hR⟩))

lemma right_child_boundary {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {s : Fin n → Bool} {r j w : ℕ} (hr : r<C.gates.length)
    (hraw : ∀k,k<C.gates.length→OrReaches n C (n+r) k→(gateAt C k).op=GateOp.or)
    (hj : j∈J n C s r) (hw : w∈(gateAt C j).inputs)
    (hout : ¬(n≤w ∧ w-n∈J n C s r)) (hR : (orIn n C w∩rightSet s).Nonempty) : w∈R n C s r := by
  rcases outside_child_pure hAO hr hraw hj hw hout with hL | hRight
  · obtain ⟨v,hv⟩ := hR
    obtain ⟨hvS,hvR⟩ := Finset.mem_inter.mp hv
    exact False.elim (Finset.disjoint_left.mp (colors_disjoint s) (hL hvS) hvR)
  · exact mem_R.mpr ⟨j,hj,hw,hRight⟩

lemma boundary_right {n : ℕ} {C : Circuit} {s : Fin n → Bool} {r w : ℕ}
    (hw : w∈R n C s r) : orIn n C w⊆rightSet s := by
  obtain ⟨j,hj,hw,hS⟩ := mem_R.mp hw
  exact hS

lemma boundary_zero_left {n : ℕ} {C : Circuit} {s : Fin n → Bool} {r w : ℕ}
    (hw : w∈R n C s r) : orIn n C w∩leftSet s=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hvS,hvL⟩ := Finset.mem_inter.mp hv
  exact Finset.disjoint_left.mp (colors_disjoint s) hvL (boundary_right hw hvS)

lemma boundary_raw {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {s : Fin n → Bool} {r w : ℕ}
    (hr : r<C.gates.length)
    (hraw : ∀k,k<C.gates.length→OrReaches n C (n+r) k→(gateAt C k).op=GateOp.or)
    (hw : w∈R n C s r) :
    ∀k,k<C.gates.length→OrReaches n C w k→(gateAt C k).op=GateOp.or := by
  obtain ⟨j,hj,hw,_⟩ := mem_R.mp hw
  exact child_raw hAO hr hraw hj hw

lemma boundary_support_subset {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {s : Fin n → Bool} {r w : ℕ} (hr : r<C.gates.length)
    (hraw : ∀k,k<C.gates.length→OrReaches n C (n+r) k→(gateAt C k).op=GateOp.or)
    (hw : w∈R n C s r) : orIn n C w⊆orIn n C (n+r) := by
  obtain ⟨j,hj,hw,_⟩ := mem_R.mp hw
  exact child_support_subset hAO hr hraw hj hw

lemma boundary_positive_root {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {s : Fin n → Bool} {r w : ℕ}
    (hraw : ∀k,k<C.gates.length→OrReaches n C (n+r) k→(gateAt C k).op=GateOp.or)
    (hw : w∈R n C s r) (x : Fin n → Bool) : W n C x w=true→W n C x (n+r)=true := by
  obtain ⟨j,hj,hw,_⟩ := mem_R.mp hw
  exact child_positive_root hAO hraw hj hw x

lemma boundary_before {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {s : Fin n → Bool} {r h : ℕ}
    (hh : h<C.gates.length) (hroot : n+r∈(gateAt C h).inputs) : ∀w∈R n C s r,w<n+h := by
  intro w hw
  obtain ⟨j,hj,hw,_⟩ := mem_R.mp hw
  have hjh := region_before hAO hh hroot j hj
  have hback := hAO.2.1 j (mem_J.mp hj).1 w hw
  omega

lemma boundary_used {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {s : Fin n → Bool} {r : ℕ} :
    ∀w∈R n C s r,∃j∈J n C s r,w=opnd C j 0 ∨ w=opnd C j 1 := by
  intro w hw
  obtain ⟨j,hj,hw,_⟩ := mem_R.mp hw
  refine ⟨j,hj,?_⟩
  simpa only [gate_inputs_eq hAO (mem_J.mp hj).1,List.mem_cons,List.not_mem_nil,or_false] using hw

lemma operand_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j<C.gates.length) (b : Fin 2) : opnd C j b∈(gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma region_operand_back {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {s : Fin n → Bool} {r : ℕ} :
    ∀j∈J n C s r,∀b:Fin 2,opnd C j b<n+j := by
  intro j hj b
  exact hAO.2.1 j (mem_J.mp hj).1 _ (operand_mem hAO (mem_J.mp hj).1 b)

lemma root_right_boundary_union {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {s : Fin n → Bool} {r : ℕ} (hr : r<C.gates.length)
    (hraw : ∀k,k<C.gates.length→OrReaches n C (n+r) k→(gateAt C k).op=GateOp.or)
    (hL : (orIn n C (n+r)∩leftSet s).Nonempty)
    (hR : (orIn n C (n+r)∩rightSet s).Nonempty) :
    orIn n C (n+r)∩rightSet s=(R n C s r).biUnion (orIn n C) := by
  apply LeftProjectionData.right_support_boundary_union (J n C s r) (R n C s r) (orIn n C)
    (rightSet s) (fun j=>opnd C j 0) (fun j=>opnd C j 1) r (root_mem hr hL hR)
    (fun j hj=>region_operand_back hAO j hj 0) (fun j hj=>region_operand_back hAO j hj 1)
    (region_union hAO hr hraw)
  · intro j hj w hw hout hNonempty
    have hwin : w∈(gateAt C j).inputs := by
      rcases hw with rfl | rfl <;> exact operand_mem hAO (mem_J.mp hj).1 _
    exact right_child_boundary hAO hr hraw hj hwin hout hNonempty
  · intro w hw
    exact boundary_support_subset hAO hr hraw hw
  · intro w hw
    exact boundary_right hw

lemma boundary_nonempty {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {s : Fin n → Bool} {r : ℕ} (hr : r<C.gates.length)
    (hraw : ∀k,k<C.gates.length→OrReaches n C (n+r) k→(gateAt C k).op=GateOp.or)
    (hL : (orIn n C (n+r)∩leftSet s).Nonempty)
    (hR : (orIn n C (n+r)∩rightSet s).Nonempty) : (R n C s r).Nonempty :=
  LeftProjectionData.right_boundary_nonempty (R n C s r) (orIn n C) (rightSet s) r
    (root_right_boundary_union hAO hr hraw hL hR) hR

lemma at_most_one_boundary_child {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {s : Fin n → Bool} {r : ℕ} (hr : r<C.gates.length)
    (hraw : ∀k,k<C.gates.length→OrReaches n C (n+r) k→(gateAt C k).op=GateOp.or) :
    ∀j∈J n C s r,¬(opnd C j 0∈R n C s r ∧ opnd C j 1∈R n C s r) :=
  LeftProjectionData.at_most_one_right_child (J n C s r) (R n C s r) (orIn n C)
    (leftSet s) (rightSet s) (fun j=>opnd C j 0) (fun j=>opnd C j 1) (colors_disjoint s)
    (region_union hAO hr hraw) (fun _j hj=>(mem_J.mp hj).2.2.1) (fun _w hw=>boundary_right hw)

lemma right_sources_le_aliases {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {s : Fin n → Bool} {r : ℕ} (hr : r<C.gates.length)
    (hraw : ∀k,k<C.gates.length→OrReaches n C (n+r) k→(gateAt C k).op=GateOp.or) :
    (R n C s r).card≤(LeftProjectionData.aliases (J n C s r) (R n C s r)
      (fun j=>opnd C j 0) (fun j=>opnd C j 1)).card :=
  LeftProjectionData.right_sources_le_aliases (J n C s r) (R n C s r)
    (fun j=>opnd C j 0) (fun j=>opnd C j 1) (boundary_used hAO) (at_most_one_boundary_child hAO hr hraw)

end CanonicalMixed

namespace ClosedLeftProjection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_5012.H5Support.Mixed (monoInput)
open Frontier LeftProjectionData

def leftSet {n : ℕ} (s : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun a => s a = false

noncomputable def valuation {n : ℕ} (C : Circuit) (J : Finset ℕ) (s : Fin n → Bool)
    (h p : ℕ) (R : Finset ℕ) (w : ℕ) (x : Fin n → Bool) : Bool :=
  LeftProjectionEval.value C J (orIn n C) (leftSet s) h p R x w

noncomputable def isAnd (C : Circuit) (j : ℕ) : Bool := by
  classical
  exact decide ((gateAt C j).op = GateOp.and)

lemma gate_binary {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (f : ℕ → Bool) :
    (gateAt C j).op.eval ((gateAt C j).inputs.map f) =
      AliasCompiler.binaryValue (isAnd C j)
        (f (opnd C j 0)) (f (opnd C j 1)) := by
  classical
  rw [gate_inputs_eq hAO hj]
  rcases gate_op_cases hAO hj with hop | hop <;>
    simp [hop,GateOp.eval,AliasCompiler.binaryValue,isAnd]

lemma no_least {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hTop : TopForm G C)
    (s : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → s a ≠ s b)
    (g h p q : ℕ) (hJunk : junk G C = {g,h})
    (hMono : gateVal n C h (monoInput s false) = true)
    (v : Fin n) (hv : s v = true)
    (hCenter : ∀ x, gateVal n C g x = true → x v = true)
    (J R : Finset ℕ)
    (hJbefore : ∀ j ∈ J, j < h)
    (hJor : ∀ j ∈ J, (gateAt C j).op = GateOp.or)
    (hMixed : ∀ j ∈ J, ∀ c : Bool, gateVal n C j (monoInput s c) = true)
    (hRaw : ∀ j ∈ J, ∀ x, W n C x (n+j) = setOr (orIn n C (n+j)) x)
    (hUnion : ∀ j ∈ J, orIn n C (n+j) =
      orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1))
    (hR : R.Nonempty) (hRback : ∀ w ∈ R, w < n+h)
    (hUsed : ∀ w ∈ R, ∃ j ∈ J, w = opnd C j 0 ∨ w = opnd C j 1)
    (hOne : ∀ j ∈ J, ¬ (opnd C j 0 ∈ R ∧ opnd C j 1 ∈ R))
    (hZero : ∀ w ∈ R, orIn n C w ∩ leftSet s = ∅)
    (hBoundary : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs,
      ¬ (n ≤ w ∧ w-n ∈ J) → w ∉ R →
      (∀ x, W n C x w = setOr (orIn n C w) x) ∧
      orIn n C w ⊆ leftSet s ∧
      (∀ k, k < C.gates.length → OrReaches n C w k → (gateAt C k).op = GateOp.or))
    (hHin : (gateAt C h).inputs = [p,q] ∨ (gateAt C h).inputs = [q,p])
    (hRcover : ∀ w ∈ R, ∀ x, W n C x w = true → W n C x q = true)
    (hPres : ∀ k ∈ junk G C, ∀ a b, G.Adj a b →
      gateVal n C k (pairInput a b) = true → valuation C J s h p R (n+k) (pairInput a b) = true) : False := by
  classical
  let U := valuation C J s h p R
  let a := fun j => opnd C j 0
  let b := fun j => opnd C j 1
  let A := aliases J R a b
  let link := aliasChild R a b
  let op := isAnd C
  have hAO := hL.1
  have hhJunk : h ∈ junk G C := by simp [hJunk]
  obtain ⟨_,hhop,hh,hhdirty⟩ := Finset.mem_filter.mp hhJunk
  have hJbound : ∀ j ∈ J, j < C.gates.length := by
    intro j hj
    have := hJbefore j hj
    omega
  have hhJ : h ∉ J := by intro hhJ; have := hJbefore h hhJ; omega
  have hp : p < n+h := hAO.2.1 h hh p (by rcases hHin with hi | hi <;> simp [hi])
  have hInputs : ∀ t : Fin n, ∀ x, U t.val x = x t := by
    intro t x
    exact LeftProjectionEval.input C J (orIn n C) (leftSet s) h p R x t.val t.isLt
  have hOR : ∀ j, j < C.gates.length → j ∉ J → (gateAt C j).op = GateOp.or → ∀ x,
      U (n+j) x = (U (opnd C j 0) x || U (opnd C j 1) x) := by
    intro j hj hjJ hjOR x
    have hjh : j ≠ h := by intro he; subst j; rw [hhop] at hjOR; contradiction
    rw [show U (n+j) x = (gateAt C j).op.eval ((gateAt C j).inputs.map (fun w => U w x)) from
      LeftProjectionEval.ordinary hAO J (orIn n C) (leftSet s) h p R x j hj hjJ hjh]
    rw [gate_binary hAO j hj]
    simp [isAnd,hjOR,AliasCompiler.binaryValue]
  have hUnder : ∀ x w, U w x = true → W n C x w = true :=
    LeftProjectionEval.under hAO J (orIn n C) (leftSet s) h p q R hh hhJ hhop hHin hRback
      (fun j _ hj => hRaw j hj) hRcover
  have hChild : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, w ∉ R → ∀ x,
      U w x = setOr (orIn n C w ∩ leftSet s) x := by
    intro j hjJ w hw hwR x
    by_cases hwJ : n ≤ w ∧ w-n ∈ J
    · have he : n+(w-n) = w := by omega
      have hval := LeftProjectionEval.region C J (orIn n C) (leftSet s) h p R x (w-n)
        (hJbound _ hwJ.2) hwJ.2
      simpa only [he,U,valuation] using hval
    · obtain ⟨hsem,hsub,hraw⟩ := hBoundary j hjJ w hw hwJ hwR
      have hvalue : U w x = W n C x w := by
        apply Bool.eq_iff_iff.mpr
        constructor
        · exact hUnder x w
        · exact MultiMixedProjection.pure_raw_wire_preserves hAO J U hInputs hOR s hMixed w
            (orIn n C w) false hsem (fun t ht => (Finset.mem_filter.mp (hsub ht)).2) hraw x
      rw [hvalue,hsem,Finset.inter_eq_left.mpr hsub]
  have hEq : ∀ j ∈ J, ∀ x, U (n+j) x =
      if a j ∈ R then U (b j) x else if b j ∈ R then U (a j) x
      else U (a j) x || U (b j) x := by
    intro j hjJ x
    apply left_gate_equation (orIn n C) (leftSet s) R a b x (fun w => U w x)
      (hUnion j hjJ) (LeftProjectionEval.region C J (orIn n C) (leftSet s) h p R x j (hJbound j hjJ) hjJ)
      (hOne j hjJ)
    · intro w hw hwR
      exact hZero w hwR
    · intro w hw hwR
      apply hChild j hjJ w _ hwR x
      rcases hw with rfl | rfl
      · exact PrivateProjection.opnd_mem hAO (hJbound j hjJ) 0
      · exact PrivateProjection.opnd_mem hAO (hJbound j hjJ) 1
  have hAb : ∀ j ∈ A, j < h := fun j hj => hJbefore j (Finset.mem_filter.mp hj).1
  have hcount : R.card ≤ A.card := right_sources_le_aliases J R a b hUsed hOne
  have hab : ∀ j < C.gates.length, a j < n+j ∧ b j < n+j := by
    intro j hj
    exact ⟨hAO.2.1 j hj _ (PrivateProjection.opnd_mem hAO hj 0),
      hAO.2.1 j hj _ (PrivateProjection.opnd_mem hAO hj 1)⟩
  have hlink : ∀ j ∈ A, link j < n+j := by
    intro j hj
    have hjJ := (Finset.mem_filter.mp hj).1
    unfold link aliasChild
    split
    · exact (hab j (hJbound j hjJ)).2
    · exact (hab j (hJbound j hjJ)).1
  have hin : ∀ w < n, ∀ x, U w x = (List.ofFn x).getD w false := by
    intro w hw x
    rw [show U w x = x ⟨w,hw⟩ from LeftProjectionEval.input C J (orIn n C) (leftSet s) h p R x w hw]
    simp [List.getD_eq_getElem?_getD,hw]
  have halias : ∀ j ∈ A, ∀ x, U (n+j) x = U (link j) x := by
    intro j hj x
    exact left_gate_alias hj (hEq j (Finset.mem_filter.mp hj).1 x)
  have hval : ∀ j < C.gates.length, j ∉ A → j ≠ h → ∀ x,
      U (n+j) x = AliasCompiler.binaryValue (op j) (U (a j) x) (U (b j) x) := by
    intro j hj hjA hjh x
    by_cases hjJ : j ∈ J
    · have heq := left_gate_binary hjJ hjA (hEq j hjJ x)
      simpa [op,isAnd,hJor j hjJ,AliasCompiler.binaryValue,U,valuation] using heq
    · exact (LeftProjectionEval.ordinary hAO J (orIn n C) (leftSet s) h p R x j hj hjJ hjh).trans
        (gate_binary hAO j hj (fun w => U w x))
  have hpatch : ∀ x, U (n+h) x = (U p x && decide (∃ w ∈ R, U w x = true)) := by
    intro x
    exact LeftProjectionEval.special C J (orIn n C) (leftSet s) h p R x hh hhJ hp hRback
  have hAND : ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.and → BelowF G C j → ∀ x,
      U (n+j) x = (U (opnd C j 0) x && U (opnd C j 1) x) := by
    intro j hj hjAND hjclean x
    have hjJ : j ∉ J := by intro he; have := hJor j he; rw [hjAND] at this; contradiction
    have hjh : j ≠ h := by
      intro he
      subst j
      obtain ⟨y,hy,hyF⟩ := hhdirty
      have := hjclean y hy
      rw [hyF] at this
      contradiction
    rw [show U (n+j) x = (gateAt C j).op.eval ((gateAt C j).inputs.map (fun w => U w x)) from
      LeftProjectionEval.ordinary hAO J (orIn n C) (leftSet s) h p R x j hj hjJ hjh]
    rw [gate_binary hAO j hj]
    simp [isAnd,hjAND,AliasCompiler.binaryValue]
  have hLift : ∀ j ∈ J, ∀ t ∈ orIn n C (n+j), s t = false → ∀ x, x t = true → U (n+j) x = true := by
    intro j hj t ht htc x hxt
    change LeftProjectionEval.value C J (orIn n C) (leftSet s) h p R x (n+j) = true
    rw [LeftProjectionEval.region C J (orIn n C) (leftSet s) h p R x j (hJbound j hj) hj]
    exact decide_eq_true ⟨t,Finset.mem_inter.mpr ⟨ht,Finset.mem_filter.mpr ⟨Finset.mem_univ t,htc⟩⟩,hxt⟩
  have hpairs := MultiMixedProjection.output_preserves_graph_pairs hAO hTop hL.2.1 s hcol g h hJunk
    hMono v hv hCenter J U hInputs hOR hAND hMixed (fun j hj x => hRaw j hj x) hLift hPres
  obtain ⟨v₀,v₁,hvv⟩ := PEqualNP.Outside.L_meta_5012.H5Support.least_nonempty_graph G C hL h hhJunk
  have hout : C.output < n+C.gates.length := by
    apply MultiMixedProjection.true_wire_bound (x := pairInput v₀ v₁)
    change circuitFun n C (pairInput v₀ v₁) = true
    rw [hL.2.1]
    exact (graphFun_pair_iff v₀ v₁).mpr hvv
  obtain ⟨E,hEAO,hsize,hEval⟩ := SpliceAlias.compile_splice n C.gates.length h p op a b link R A U
    hh hR hRback hp hAb hcount hab hlink hin halias hval hpatch C.output hout
  apply MultiMixedProjection.no_least_compiled_projection hL U hpairs (fun x => hUnder x C.output)
    E hEAO _ hEval
  exact hsize

end ClosedLeftProjection

namespace OppositeSemiMixed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_5012.H5Support.Mixed (monoInput and_true_operands and_two opnd_mem opnd_lt mixed_wire_not_input)

lemma no_pure_singleton_semimixed_opposite_color {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀a b,G.Adj a b → s a≠s b)
    (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hne : g≠h) (hJunk : junk G C={g,h})
    (hgh : ¬InCone n C g h) (hhg : ¬InCone n C h g)
    (c d : Fin 2) (v : Fin n) (hgv : side (n := n) C g c={v}) (hv : s v=true)
    (hB : ∀u∈side (n := n) C g (1-c),s u=false)
    (hA : ∀u∈side (n := n) C h d,s u=false)
    (hSleft : ∃u∈side (n := n) C h (1-d),s u=false)
    (hSright : ∃u∈side (n := n) C h (1-d),s u=true)
    (hdis : Disjoint (side (n := n) C h d) (side (n := n) C h (1-d))) : False := by
  classical
  have hAO := hL.1
  have hgJ : g∈junk G C := by simp [hJunk]
  have hhJ : h∈junk G C := by simp [hJunk]
  obtain ⟨_,hgand,hglen,_⟩ := Finset.mem_filter.mp hgJ
  obtain ⟨_,hhand,hhlen,xh,hhx,hhFx⟩ := Finset.mem_filter.mp hhJ
  have hJiff : ∀k,k∈junk G C ↔ k=g ∨ k=h := by intro k; simp [hJunk]
  have hJswap : ∀k,k∈junk G C ↔ k=h ∨ k=g := by intro k; simp [hJunk,or_comm]
  have hgRaw (b : Fin 2) : ∀k,k<C.gates.length → OrReaches n C (opnd C g b) k →
      (gateAt C k).op=GateOp.or :=
    SingletonFlagProjection.independent_operand_raw hAO hTop hglen hgand hJiff hhg (opnd_mem hAO hglen b)
  have hhRaw (b : Fin 2) : ∀k,k<C.gates.length → OrReaches n C (opnd C h b) k →
      (gateAt C k).op=GateOp.or :=
    SingletonFlagProjection.independent_operand_raw hAO hTop hhlen hhand hJswap hgh (opnd_mem hAO hhlen b)
  have hgSem (b : Fin 2) (x : Fin n → Bool) :
      Frontier.W n C x (opnd C g b)=setOr (side (n := n) C g b) x :=
    SingletonPrivacy.W_eq_setOr_of_raw hAO _ (hgRaw b) x
  have hhSem (b : Fin 2) (x : Fin n → Bool) :
      Frontier.W n C x (opnd C h b)=setOr (side (n := n) C h b) x :=
    SingletonPrivacy.W_eq_setOr_of_raw hAO _ (hhRaw b) x
  have hCenter (x : Fin n → Bool) (hx : gateVal n C g x=true) : x v=true := by
    have hc := and_true_operands hAO hglen hgand x hx c
    change Frontier.W n C x (opnd C g c)=true at hc
    rw [hgSem,hgv] at hc
    simpa [setOr] using hc
  have hMono : gateVal n C h (monoInput s false)=true := by
    have had := and_true_operands hAO hhlen hhand xh hhx d
    change Frontier.W n C xh (opnd C h d)=true at had
    rw [hhSem] at had
    obtain ⟨a,ha,_⟩ := of_decide_eq_true had
    obtain ⟨b,hb,hbc⟩ := hSleft
    apply and_two hAO hhlen hhand d (monoInput s false)
    · change Frontier.W n C (monoInput s false) (opnd C h d)=true
      rw [hhSem]
      exact decide_eq_true ⟨a,ha,by simp [monoInput,hA a ha]⟩
    · change Frontier.W n C (monoInput s false) (opnd C h (1-d))=true
      rw [hhSem]
      exact decide_eq_true ⟨b,hb,by simp [monoInput,hbc]⟩
  let p := opnd C h d
  let q := opnd C h (1-d)
  have hHin : (gateAt C h).inputs=[p,q] ∨ (gateAt C h).inputs=[q,p] := by
    rw [Frontier.gate_inputs_eq hAO hhlen]
    fin_cases d
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hqMixed (b : Bool) : PEqualNP.Outside.L_meta_5012.H5Support.Mixed.W n C (monoInput s b) q=true := by
    change Frontier.W n C (monoInput s b) (opnd C h (1-d))=true
    rw [hhSem]
    cases b
    · obtain ⟨u,hu,huc⟩ := hSleft
      exact decide_eq_true ⟨u,hu,by simp [monoInput,huc]⟩
    · obtain ⟨u,hu,huc⟩ := hSright
      exact decide_eq_true ⟨u,hu,by simp [monoInput,huc]⟩
  have hqn : n≤q := by have := mixed_wire_not_input hqMixed; omega
  have hqb : q<n+h := opnd_lt hAO hhlen (1-d)
  let r := q-n
  have heq : n+r=q := by dsimp only [r]; omega
  have hr : r<C.gates.length := by omega
  have hRoot : n+r∈(gateAt C h).inputs := by
    rw [heq]
    exact opnd_mem hAO hhlen (1-d)
  have hRawRoot : ∀k,k<C.gates.length → OrReaches n C (n+r) k → (gateAt C k).op=GateOp.or := by
    rw [heq]
    exact hhRaw (1-d)
  have hLeft : (orIn n C (n+r)∩CanonicalMixed.leftSet s).Nonempty := by
    rw [heq]
    obtain ⟨u,hu,huc⟩ := hSleft
    exact ⟨u,Finset.mem_inter.mpr ⟨hu,by simp [CanonicalMixed.leftSet,huc]⟩⟩
  have hRight : (orIn n C (n+r)∩CanonicalMixed.rightSet s).Nonempty := by
    rw [heq]
    obtain ⟨u,hu,huc⟩ := hSright
    exact ⟨u,Finset.mem_inter.mpr ⟨hu,by simp [CanonicalMixed.rightSet,huc]⟩⟩
  let J := CanonicalMixed.J n C s r
  let R := CanonicalMixed.R n C s r
  have hMixed : ∀j∈J,∀b : Bool,gateVal n C j (monoInput s b)=true := by
    intro j hj b
    change Frontier.W n C (monoInput s b) (n+j)=true
    rw [CanonicalMixed.region_value hAO hr hRawRoot j hj]
    have hjdata := CanonicalMixed.mem_J.mp hj
    cases b
    · obtain ⟨u,hu⟩ := hjdata.2.2.1
      obtain ⟨huS,huColor⟩ := Finset.mem_inter.mp hu
      have huc : s u=false := (Finset.mem_filter.mp huColor).2
      exact decide_eq_true ⟨u,huS,by simp [monoInput,huc]⟩
    · obtain ⟨u,hu⟩ := hjdata.2.2.2
      obtain ⟨huS,huColor⟩ := Finset.mem_inter.mp hu
      have huc : s u=true := (Finset.mem_filter.mp huColor).2
      exact decide_eq_true ⟨u,huS,by simp [monoInput,huc]⟩
  have hRback : ∀w∈R,w<n+h := CanonicalMixed.boundary_before hAO hhlen hRoot
  have hRcolor : ∀w∈R,∀u∈orIn n C w,s u=true := by
    intro w hw u hu
    exact (Finset.mem_filter.mp (CanonicalMixed.boundary_right hw hu)).2
  have hCover : (orIn n C q).filter (fun u => s u=true)=R.biUnion (orIn n C) := by
    have he : (orIn n C q).filter (fun u => s u=true)=orIn n C q∩CanonicalMixed.rightSet s := by
      ext u
      simp [CanonicalMixed.rightSet]
    rw [he]
    simpa only [heq] using CanonicalMixed.root_right_boundary_union hAO hr hRawRoot hLeft hRight
  have hgColors : ∀b : Fin 2,∃cc : Bool,∀u∈side (n := n) C g b,s u=cc := by
    intro b
    by_cases hb : b=c
    · subst b
      refine ⟨true,?_⟩
      intro u hu
      rw [hgv,Finset.mem_singleton] at hu
      simpa only [hu] using hv
    · have hb' : b=1-c := by fin_cases b <;> fin_cases c <;> simp_all
      subst b
      exact ⟨false,hB⟩
  have hPres : ∀k∈junk G C,∀a b,G.Adj a b → gateVal n C k (pairInput a b)=true →
      ClosedLeftProjection.valuation C J s h p R (n+k) (pairInput a b)=true := by
    exact LeftProjectionPreservation.junk_pairs_preserved hAO s hcol g h p q hne hJunk hHin
      J (ClosedLeftProjection.leftSet s) R (CanonicalMixed.region_or hRawRoot) hMixed hgColors hgRaw
      hA (hhRaw d) (hhRaw (1-d)) hdis hRback hRcolor
      (fun w hw => CanonicalMixed.boundary_raw hAO hr hRawRoot hw) hCover
  apply ClosedLeftProjection.no_least hL hTop s hcol g h p q hJunk hMono v hv hCenter J R
    (CanonicalMixed.region_before hAO hhlen hRoot) (CanonicalMixed.region_or hRawRoot) hMixed
    (CanonicalMixed.region_value hAO hr hRawRoot) (CanonicalMixed.region_union hAO hr hRawRoot)
    (CanonicalMixed.boundary_nonempty hAO hr hRawRoot hLeft hRight) hRback
    (CanonicalMixed.boundary_used hAO) (CanonicalMixed.at_most_one_boundary_child hAO hr hRawRoot)
    (fun w hw => CanonicalMixed.boundary_zero_left hw) _ hHin _ hPres
  · intro j hj w hw hout hnot
    exact ⟨CanonicalMixed.child_value hAO hr hRawRoot hj hw,
      CanonicalMixed.outside_not_right_left hAO hr hRawRoot hj hw hout hnot,
      CanonicalMixed.child_raw hAO hr hRawRoot hj hw⟩
  · intro w hw x hx
    have hq := CanonicalMixed.boundary_positive_root hAO hRawRoot hw x hx
    simpa only [heq] using hq

lemma no_pure_singleton_semimixed_left_factor {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀a b,G.Adj a b → s a≠s b)
    (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hne : g≠h) (hJunk : junk G C={g,h})
    (hgh : ¬InCone n C g h) (hhg : ¬InCone n C h g)
    (c d : Fin 2) (v : Fin n) (hgv : side (n := n) C g c={v})
    (hB : ∀u∈side (n := n) C g (1-c),s u= !(s v))
    (hA : ∀u∈side (n := n) C h d,s u=false)
    (hSleft : ∃u∈side (n := n) C h (1-d),s u=false)
    (hSright : ∃u∈side (n := n) C h (1-d),s u=true)
    (hdis : Disjoint (side (n := n) C h d) (side (n := n) C h (1-d))) : False := by
  cases hv : s v with
  | false =>
    apply SemiMixedSingleton.no_pure_singleton_semimixed_same_color G C s hcol hL hTop
      g h hJunk hgh hhg c d v hgv hv _ hA hSleft hSright hdis
    intro u hu
    simpa only [hv,Bool.not_false] using hB u hu
  | true =>
    apply no_pure_singleton_semimixed_opposite_color G C s hcol hL hTop g h hne hJunk
      hgh hhg c d v hgv hv _ hA hSleft hSright hdis
    intro u hu
    simpa only [hv,Bool.not_true] using hB u hu

lemma no_pure_singleton_semimixed {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀a b,G.Adj a b → s a≠s b)
    (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hne : g≠h) (hJunk : junk G C={g,h})
    (hgh : ¬InCone n C g h) (hhg : ¬InCone n C h g)
    (c d : Fin 2) (v : Fin n) (hgv : side (n := n) C g c={v})
    (hB : ∀u∈side (n := n) C g (1-c),s u= !(s v))
    (hA : ∃b : Bool,∀u∈side (n := n) C h d,s u=b)
    (hSleft : ∃u∈side (n := n) C h (1-d),s u=false)
    (hSright : ∃u∈side (n := n) C h (1-d),s u=true)
    (hdis : Disjoint (side (n := n) C h d) (side (n := n) C h (1-d))) : False := by
  obtain ⟨b,hA⟩ := hA
  cases b
  · exact no_pure_singleton_semimixed_left_factor G C s hcol hL hTop g h hne hJunk
      hgh hhg c d v hgv hB hA hSleft hSright hdis
  · have hbip : ∀a b,G.Adj a b → (!(s a))≠(!(s b)) := by
      intro a b hab he
      apply hcol a b hab
      simpa using congrArg Bool.not he
    apply no_pure_singleton_semimixed_left_factor G C (fun u => !(s u)) hbip hL hTop g h hne hJunk
      hgh hhg c d v hgv _ _ _ _ hdis
    · intro u hu
      exact congrArg Bool.not (hB u hu)
    · intro u hu
      simp only [hA u hu,Bool.not_true]
    · obtain ⟨u,hu,huc⟩ := hSright
      exact ⟨u,hu,by simp only [huc,Bool.not_true]⟩
    · obtain ⟨u,hu,huc⟩ := hSleft
      exact ⟨u,hu,by simp only [huc,Bool.not_false]⟩

end OppositeSemiMixed

end PEqualNP.Outside.L_meta_5012
