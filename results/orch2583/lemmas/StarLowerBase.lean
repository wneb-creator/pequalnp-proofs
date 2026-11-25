import PEqualNP.Defs

-- General graph covering bound from the checked proof of L-meta-2237.
namespace PEqualNP.Outside.L_meta_2583.ReadLower.General


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def s2230_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2230_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2230_stepWire x := rfl

lemma s2230_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2230_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2230_stepWire]
    omega

lemma s2230_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2230_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2230_stepWire w g).length := by simp [s2230_stepWire]; omega
    rw [ih (s2230_stepWire w g) hlt]
    simp [s2230_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2230_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2230_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [s2230_wires_eq_foldl, s2230_foldl_stepWire_length, List.length_ofFn]

lemma s2230_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def s2230_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma s2230_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma s2230_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    s2230_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then s2230_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2230_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [s2230_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl s2230_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, s2230_foldl_stepWire_length, hpre_len]
  have hCj : s2230_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [s2230_W]
    rw [s2230_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [s2230_foldl_stepWire_getD_lt post (s2230_stepWire w0 gj) (n + k) (by simp [s2230_stepWire]; omega)]
    simp [s2230_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [s2230_W]
    rw [s2230_wires_eq_foldl, hgs, List.foldl_append]
    exact (s2230_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact s2230_getD_ge_length w0 i (by omega)

lemma s2230_W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    s2230_W n C x u = x ⟨u, hu⟩ := by
  simp only [s2230_W]
  rw [s2230_wires_eq_foldl, s2230_foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma s2230_orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma s2230_orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
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
lemma s2230_orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma s2230_orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact s2230_orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma s2230_orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := s2230_split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [s2230_gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [s2230_orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, s2230_orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, s2230_orFold_getD_lt n post _ m (by omega)]
    exact s2230_orStep_getD_lt n _ gk m (by omega)
  have h3 := s2230_orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩

open PEqualNP.CleanedNonEdge PEqualNP.ReadK PEqualNP.TopForm

lemma s2230_orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) j := by
  unfold OrReaches
  refine ⟨Nat.le_add_right n j, ?_⟩
  rw [Nat.add_sub_cancel_left, s2230_orSets_mem_iff n C j j hj]
  exact Or.inl rfl

lemma s2230_orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : OrReaches n C i g) : OrReaches n C (n + j) g := by
  unfold OrReaches at h ⊢
  refine ⟨Nat.le_add_right n j, ?_⟩
  rw [Nat.add_sub_cancel_left, s2230_orSets_mem_iff n C j g hj]
  exact Or.inr ⟨hop, i, hi, h.1, hlt, h.2⟩

lemma s2230_mem_filter_iff_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

lemma s2230_mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold orIn
  exact ⟨fun h => ((s2230_mem_filter_iff_gen _ _ _ _).1 h).2,
    fun h => (s2230_mem_filter_iff_gen _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

lemma s2230_orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ orIn n C i) : a ∈ orIn n C (n + j) := by
  rw [s2230_mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, s2230_orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, s2230_orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩

def s2230_FR (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

def s2230_stepR (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) :=
  R ++ [s2230_FR S k R g]

lemma s2230_readVectors_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = C.gates.foldl (s2230_stepR S k) ((List.range n).map (leafVectors S k)) := by
  first
    | rfl
    | (unfold readVectors; congr 1; funext R g; rcases g with ⟨op, ins⟩; cases op <;> rfl)

lemma s2230_FR_or (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) (h : g.op = GateOp.or) :
    s2230_FR S k R g =
      (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) [] := by
  obtain ⟨op, ins⟩ := g
  have h2 : op = GateOp.or := h
  subst h2
  rfl

lemma s2230_FR_and (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate)
    (h : g.op = GateOp.and) :
    s2230_FR S k R g = (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0] := by
  obtain ⟨op, ins⟩ := g
  have h2 : op = GateOp.and := h
  subst h2
  rfl

lemma s2230_foldR_length (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) :
    (gs.foldl (s2230_stepR S k) R).length = R.length + gs.length := by
  induction gs generalizing R with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2230_stepR]
    omega

lemma s2230_foldR_getD_lt (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) (i : ℕ)
    (hi : i < R.length) : (gs.foldl (s2230_stepR S k) R).getD i [] = R.getD i [] := by
  induction gs generalizing R with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2230_stepR S k R g).length := by simp [s2230_stepR]; omega
    rw [ih (s2230_stepR S k R g) hlt]
    simp [s2230_stepR, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def s2230_RV (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) : List (List ℕ) :=
  (readVectors C n S k).getD w []

lemma s2230_RV_input (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) (hw : w < n) :
    s2230_RV C n S k w = leafVectors S k w := by
  simp only [s2230_RV]
  rw [s2230_readVectors_eq, s2230_foldR_getD_lt S k C.gates ((List.range n).map (leafVectors S k)) w
    (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma s2230_RV_gate (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (j : ℕ) (hj : j < C.gates.length) :
    ∃ Rp : List (List (List ℕ)),
      (∀ i, i < n + j → Rp.getD i [] = s2230_RV C n S k i) ∧
      s2230_RV C n S k (n + j) = s2230_FR S k Rp (gateAt C j) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2230_split_gates C.gates j hj
  have hga : gateAt C j = gj := by rw [s2230_gateAt_eq C j hj]; exact hgj
  rw [hga]
  obtain ⟨Rp, hRp⟩ : ∃ Rp, Rp = pre.foldl (s2230_stepR S k) ((List.range n).map (leafVectors S k)) :=
    ⟨_, rfl⟩
  have hlen : Rp.length = n + j := by
    rw [hRp, s2230_foldR_length]
    simp only [List.length_map, List.length_range, hpre_len]
  have hall : readVectors C n S k = post.foldl (s2230_stepR S k) (s2230_stepR S k Rp gj) := by
    rw [s2230_readVectors_eq, hgs, List.foldl_append, List.foldl_cons, hRp]
  have hlen1 : (s2230_stepR S k Rp gj).length = n + j + 1 := by
    simp [s2230_stepR, hlen]
  refine ⟨Rp, ?_, ?_⟩
  · intro i hi
    simp only [s2230_RV]
    rw [hall, s2230_foldR_getD_lt S k post (s2230_stepR S k Rp gj) i (by omega)]
    simp [s2230_stepR, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show i < Rp.length by omega)]
  · simp only [s2230_RV]
    rw [hall, s2230_foldR_getD_lt S k post (s2230_stepR S k Rp gj) (n + j) (by omega)]
    simp [s2230_stepR, List.getD_eq_getElem?_getD, hlen]

lemma s2230_mem_foldl_insertNew (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ L.foldl insertNew acc) : v ∈ acc ∨ v ∈ L := by
  induction L generalizing acc with
  | nil => exact Or.inl h
  | cons x L ih =>
    rw [List.foldl_cons] at h
    rcases ih _ h with h1 | h1
    · unfold insertNew at h1
      split_ifs at h1
      · exact Or.inl h1
      · rcases List.mem_append.1 h1 with h2 | h2
        · exact Or.inl h2
        · have h3 : v = x := by simpa using h2
          exact Or.inr (by simp [h3])
    · exact Or.inr (List.mem_cons_of_mem _ h1)

lemma s2230_mem_andStep (k : ℕ) (A B : List (List ℕ)) (v : List ℕ) (h : v ∈ andStep k A B) :
    ∃ u ∈ A, ∃ u2 ∈ B, v = capAdd k u u2 := by
  unfold andStep at h
  rcases s2230_mem_foldl_insertNew _ _ _ h with h1 | h1
  · simp at h1
  · simp only [List.mem_flatMap, List.mem_map] at h1
    obtain ⟨u, hu, u2, hu2, rfl⟩ := h1
    exact ⟨u, hu, u2, hu2, rfl⟩

lemma s2230_capAdd_pair (k x1 y1 x2 y2 : ℕ) :
    capAdd k [x1, y1] [x2, y2] = [min (x1 + x2) (k + 1), min (y1 + y2) (k + 1)] := by
  first
    | rfl
    | simp [capAdd]

lemma s2230_leaf_eq (a b w : ℕ) :
    leafVectors [a, b] 1 w =
      if w ∈ [a, b] then [[if a = w then 1 else 0, if b = w then 1 else 0]] else [] := by
  first
    | rfl
    | (unfold leafVectors; simp)

theorem s2230_inv (n : ℕ) (C : Circuit) (a b : Fin n) (hC : IsAO2 n C) (hab : a.val < b.val) :
    ∀ w : ℕ, ∀ v ∈ s2230_RV C n [a.val, b.val] 1 w, ∃ x y : ℕ, v = [x, y] ∧ 1 ≤ x + y ∧
      (x = 1 → y = 0 →
        a ∈ orIn n C w ∧ s2230_W n C (fun k1 : Fin n => decide (k1 = a)) w = true) ∧
      (x = 0 → y = 1 →
        b ∈ orIn n C w ∧ s2230_W n C (fun k1 : Fin n => decide (k1 = b)) w = true) ∧
      (x = 1 → y = 1 → ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
        OrReaches n C w j ∧
        ((a ∈ side (n := n) C j 0 ∧ b ∈ side (n := n) C j 1) ∨
          (b ∈ side (n := n) C j 0 ∧ a ∈ side (n := n) C j 1))) := by
  obtain ⟨hAnd, hBack, hTwo⟩ := hC
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv
    by_cases hwn : w < n
    · rw [s2230_RV_input C n _ 1 w hwn, s2230_leaf_eq] at hv
      by_cases hwa : a.val = w
      · have hwb : ¬ b.val = w := by omega
        rw [if_pos (List.mem_cons.2 (Or.inl hwa.symm)), if_pos hwa, if_neg hwb] at hv
        have hv2 : v = [1, 0] := List.mem_singleton.1 hv
        refine ⟨1, 0, hv2, by omega, ?_, ?_, ?_⟩
        · intro _ _
          refine ⟨?_, ?_⟩
          · rw [s2230_mem_orIn]
            exact Or.inl hwa
          · rw [s2230_W_input n C _ w hwn]
            exact decide_eq_true (Fin.ext hwa.symm)
        · intro h3 h4
          omega
        · intro h3 h4
          omega
      · by_cases hwb : b.val = w
        · rw [if_pos (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl hwb.symm)))),
            if_neg hwa, if_pos hwb] at hv
          have hv2 : v = [0, 1] := List.mem_singleton.1 hv
          refine ⟨0, 1, hv2, by omega, ?_, ?_, ?_⟩
          · intro h3 h4
            omega
          · intro _ _
            refine ⟨?_, ?_⟩
            · rw [s2230_mem_orIn]
              exact Or.inl hwb
            · rw [s2230_W_input n C _ w hwn]
              exact decide_eq_true (Fin.ext hwb.symm)
          · intro h3 h4
            omega
        · exfalso
          have hm : ¬ w ∈ [a.val, b.val] := by
            intro hm
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
            omega
          rw [if_neg hm] at hv
          simp at hv
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      by_cases hj : j < C.gates.length
      · have hmem : gateAt C j ∈ C.gates := by
          rw [s2230_gateAt_eq C j hj]
          exact List.getElem_mem hj
        have hlen2 := hTwo _ hmem
        have hback := hBack j hj
        obtain ⟨Rp, hRp, hRV⟩ := s2230_RV_gate C n [a.val, b.val] 1 j hj
        rcases hinp : (gateAt C j).inputs with _ | ⟨i1, _ | ⟨i2, _ | ⟨i3, rest⟩⟩⟩
        · exfalso
          rw [hinp] at hlen2
          simp at hlen2
        · exfalso
          rw [hinp] at hlen2
          simp at hlen2
        · have hm1 : i1 ∈ (gateAt C j).inputs := by rw [hinp]; simp
          have hm2 : i2 ∈ (gateAt C j).inputs := by rw [hinp]; simp
          have hi1 : i1 < n + j := hback i1 hm1
          have hi2 : i2 < n + j := hback i2 hm2
          rcases hAnd _ hmem with hop | hop
          · rw [hRV, s2230_FR_and _ _ _ _ hop, hinp] at hv
            simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
              hRp i1 hi1, hRp i2 hi2] at hv
            obtain ⟨t, ht, u2, hu2, rfl⟩ := s2230_mem_andStep _ _ _ _ hv
            obtain ⟨z, hz, u1, hu1, rfl⟩ := s2230_mem_andStep _ _ _ _ ht
            have hz2 : z = [0, 0] := by simpa using hz
            subst hz2
            obtain ⟨x1, y1, rfl, h1, ha1, hb1, _⟩ := ih i1 hi1 u1 hu1
            obtain ⟨x2, y2, rfl, h2, ha2, hb2, _⟩ := ih i2 hi2 u2 hu2
            refine ⟨min (min (0 + x1) (1 + 1) + x2) (1 + 1),
              min (min (0 + y1) (1 + 1) + y2) (1 + 1), ?_, by omega, ?_, ?_, ?_⟩
            · rw [s2230_capAdd_pair, s2230_capAdd_pair]
            · intro hx hy
              omega
            · intro hx hy
              omega
            · intro hx hy
              have hcase : (x1 = 1 ∧ y1 = 0 ∧ x2 = 0 ∧ y2 = 1) ∨
                  (x1 = 0 ∧ y1 = 1 ∧ x2 = 1 ∧ y2 = 0) := by omega
              refine ⟨j, hj, hop, s2230_orReaches_self n C j hj, ?_⟩
              have hs0 : side (n := n) C j 0 = orIn n C i1 := by
                first
                  | (unfold side opnd; rw [hinp]; rfl)
                  | simp [side, opnd, hinp]
              have hs1 : side (n := n) C j 1 = orIn n C i2 := by
                first
                  | (unfold side opnd; rw [hinp]; rfl)
                  | simp [side, opnd, hinp]
              rw [hs0, hs1]
              rcases hcase with ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩
              · exact Or.inl ⟨(ha1 e1 e2).1, (hb2 e3 e4).1⟩
              · exact Or.inr ⟨(hb1 e1 e2).1, (ha2 e3 e4).1⟩
          · rw [hRV, s2230_FR_or _ _ _ _ hop, hinp] at hv
            simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
              hRp i1 hi1, hRp i2 hi2] at hv
            have hsrc : ∃ i, i ∈ (gateAt C j).inputs ∧ i < n + j ∧
                v ∈ s2230_RV C n [a.val, b.val] 1 i := by
              rcases s2230_mem_foldl_insertNew _ _ _ hv with h | h
              · rcases s2230_mem_foldl_insertNew _ _ _ h with h3 | h3
                · simp at h3
                · exact ⟨i1, hm1, hi1, h3⟩
              · exact ⟨i2, hm2, hi2, h⟩
            obtain ⟨i, him, hilt, hvi⟩ := hsrc
            obtain ⟨x, y, hxy, h1, ha1, hb1, hab1⟩ := ih i hilt v hvi
            have hW : ∀ z : Fin n → Bool, s2230_W n C z i = true → s2230_W n C z (n + j) = true := by
              intro z hz
              rw [s2230_W_gate n C z j hj, hop]
              simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
              exact ⟨i, him, by simp only [hilt, ite_true]; exact hz⟩
            refine ⟨x, y, hxy, h1, ?_, ?_, ?_⟩
            · intro hx hy
              exact ⟨s2230_orIn_up n C j i a hj hop him hilt (ha1 hx hy).1, hW _ (ha1 hx hy).2⟩
            · intro hx hy
              exact ⟨s2230_orIn_up n C j i b hj hop him hilt (hb1 hx hy).1, hW _ (hb1 hx hy).2⟩
            · intro hx hy
              obtain ⟨j2, hj2, hop2, hr2, hsd⟩ := hab1 hx hy
              exact ⟨j2, hj2, hop2, s2230_orReaches_step n C j i j2 hj hop him hilt hr2, hsd⟩
        · exfalso
          rw [hinp] at hlen2
          simp at hlen2 <;> omega
      · exfalso
        have hnil : s2230_RV C n [a.val, b.val] 1 (n + j) = [] := by
          simp only [s2230_RV]
          rw [s2230_readVectors_eq]
          exact List.getD_eq_default _ _ (by
            rw [s2230_foldR_length]
            simp only [List.length_map, List.length_range]
            omega)
        rw [hnil] at hv
        simp at hv

theorem s2230 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : Fin n), PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → a < b → PEqualNP.ReadK.readsAtMost C n [a.val, b.val] 1 = true → ∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j ∧ ((a ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ b ∈ PEqualNP.TopForm.side (n := n) C j 1) ∨ (b ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ a ∈ PEqualNP.TopForm.side (n := n) C j 1)) := by
  intro n C a b hC hsingle hab hread
  have hlt : a.val < b.val := hab
  unfold readsAtMost at hread
  rw [List.any_eq_true] at hread
  obtain ⟨v, hv, hall⟩ := hread
  obtain ⟨x, y, rfl, h1, ha, hb, hab2⟩ := s2230_inv n C a b hC hlt C.output v hv
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hall
  obtain ⟨hx, hy⟩ := hall
  have hcases : (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 1) := by omega
  rcases hcases with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exfalso
    have h3 : circuitFun n C (fun k1 : Fin n => decide (k1 = a)) = true := (ha e1 e2).2
    rw [hsingle a] at h3
    exact Bool.false_ne_true h3
  · exfalso
    have h3 : circuitFun n C (fun k1 : Fin n => decide (k1 = b)) = true := (hb e1 e2).2
    rw [hsingle b] at h3
    exact Bool.false_ne_true h3
  · exact hab2 e1 e2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def s2231_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2231_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2231_stepWire x := rfl

lemma s2231_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2231_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2231_stepWire]
    omega

lemma s2231_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2231_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2231_stepWire w g).length := by simp [s2231_stepWire]; omega
    rw [ih (s2231_stepWire w g) hlt]
    simp [s2231_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2231_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2231_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [s2231_wires_eq_foldl, s2231_foldl_stepWire_length, List.length_ofFn]

lemma s2231_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def s2231_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma s2231_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma s2231_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    s2231_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then s2231_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2231_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [s2231_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl s2231_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, s2231_foldl_stepWire_length, hpre_len]
  have hCj : s2231_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [s2231_W]
    rw [s2231_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [s2231_foldl_stepWire_getD_lt post (s2231_stepWire w0 gj) (n + k) (by simp [s2231_stepWire]; omega)]
    simp [s2231_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [s2231_W]
    rw [s2231_wires_eq_foldl, hgs, List.foldl_append]
    exact (s2231_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact s2231_getD_ge_length w0 i (by omega)

lemma s2231_W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    s2231_W n C x u = x ⟨u, hu⟩ := by
  simp only [s2231_W]
  rw [s2231_wires_eq_foldl, s2231_foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma s2231_orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma s2231_orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
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
lemma s2231_orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma s2231_orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact s2231_orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma s2231_orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := s2231_split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [s2231_gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [s2231_orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, s2231_orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, s2231_orFold_getD_lt n post _ m (by omega)]
    exact s2231_orStep_getD_lt n _ gk m (by omega)
  have h3 := s2231_orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩


lemma s2231_W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.or) (i : ℕ) (hi : i ∈ (gateAt C r).inputs)
    (hlt : i < n + r) (hv : s2231_W n C x i = true) : s2231_W n C x (n + r) = true := by
  rw [s2231_W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  exact ⟨i, hi, by rw [if_pos hlt]; exact hv⟩

lemma s2231_W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and)
    (h : ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ s2231_W n C x i = true) :
    s2231_W n C x (n + r) = true := by
  rw [s2231_W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  intro i hi
  rw [if_pos (h i hi).1]; exact (h i hi).2

open PEqualNP.CleanedNonEdge in
lemma s2231_reach_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : s2231_W n C x (n + g) = true) :
    ∀ k, k < C.gates.length → g ∈ (orSets n C).getD k [] → s2231_W n C x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hmem
    rcases (s2231_orSets_mem_iff n C k g hk).mp hmem with h | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [← h]; exact hv
    · have h3 := ih (w - n) (by omega) (by omega) hx
      have e : n + (w - n) = w := by omega
      rw [e] at h3
      exact s2231_W_or n C x k hk hop w hw hlt h3

open PEqualNP.CleanedNonEdge in
lemma s2231_reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w g : ℕ)
    (h : OrReaches n C w g) (hv : s2231_W n C x (n + g) = true) : s2231_W n C x w = true := by
  obtain ⟨hn, hmem⟩ := h
  by_cases hk : w - n < C.gates.length
  · have h3 := s2231_reach_val n C x g hv (w - n) hk hmem
    have e : n + (w - n) = w := by omega
    rw [e] at h3
    exact h3
  · exfalso
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets; rw [s2231_orFold_length]; simp
    have hge : (orSets n C).length ≤ w - n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
    simp at hmem

lemma s2231_mem_filter_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α)
    (h : a ∈ @Finset.filter α p d s) : p a :=
  ((@Finset.mem_filter α p d s a).mp h).2

lemma s2231_side_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (b : Fin 2) (i : Fin n)
    (hi : i ∈ PEqualNP.TopForm.side (n := n) C j b) (hx : x i = true) :
    s2231_W n C x (PEqualNP.TopForm.opnd C j b) = true := by
  unfold PEqualNP.TopForm.side PEqualNP.TopForm.orIn at hi
  have hi2 := s2231_mem_filter_gen _ _ _ _ hi
  rcases hi2 with h | ⟨k, hk, hreach, hop, hin⟩
  · rw [← h, s2231_W_input n C x i.val i.isLt]; exact hx
  · have hk1 : s2231_W n C x (n + k) = true := by
      apply s2231_W_or n C x k hk hop i.val hin (by have := i.isLt; omega)
      rw [s2231_W_input n C x i.val i.isLt]; exact hx
    exact s2231_reach_up n C x _ k hreach hk1

def s2231_px {n : ℕ} (u v : Fin n) : Fin n → Bool := fun k => decide (k = u ∨ k = v)

lemma s2231_px_self {n : ℕ} (t : Fin n) : s2231_px t t = (fun k : Fin n => decide (k = t)) := by
  funext k; simp [s2231_px]

lemma s2231_part1 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hNF : PEqualNP.TopForm.NoFourCycle G) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (h1 : ∀ a1 : Fin n, circuitFun n C (fun k1 => decide (k1 = a1)) = false)
    (h2 : ∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 →
      circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C C.output j) :
    (∀ w : Fin n, w ∈ PEqualNP.TopForm.side (n := n) C j 0 →
        w ∉ PEqualNP.TopForm.side (n := n) C j 1) ∧
      (∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 →
        ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → G.Adj u v) ∧
      ((PEqualNP.TopForm.side (n := n) C j 0).card ≤ 1 ∨
        (PEqualNP.TopForm.side (n := n) C j 1).card ≤ 1) := by
  obtain ⟨_, hRB, hlen2⟩ := hAO
  have hgm : gateAt C j ∈ C.gates := by rw [s2231_gateAt_eq C j hj]; exact List.getElem_mem hj
  have hl2 : (gateAt C j).inputs.length = 2 := hlen2 _ hgm
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a0, b0, hl⟩ := List.length_eq_two.mp hl2
  have e0 : PEqualNP.TopForm.opnd C j 0 = a0 := by
    unfold PEqualNP.TopForm.opnd; rw [hl]; rfl
  have e1 : PEqualNP.TopForm.opnd C j 1 = b0 := by
    unfold PEqualNP.TopForm.opnd; rw [hl]; rfl
  have hcross : ∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 →
      ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → u ≠ v ∧ G.Adj u v := by
    intro u hu v hv
    have hxu : s2231_px u v u = true := by simp [s2231_px]
    have hxv : s2231_px u v v = true := by simp [s2231_px]
    have va := s2231_side_val n C (s2231_px u v) j 0 u hu hxu
    have vb := s2231_side_val n C (s2231_px u v) j 1 v hv hxv
    rw [e0] at va
    rw [e1] at vb
    have hg : s2231_W n C (s2231_px u v) (n + j) = true := by
      apply s2231_W_and n C (s2231_px u v) j hj hop
      intro i hi
      have hi2 := hi
      rw [hl] at hi2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi2
      rcases hi2 with h | h
      · exact ⟨hrb i hi, by rw [h]; exact va⟩
      · exact ⟨hrb i hi, by rw [h]; exact vb⟩
    have hW : circuitFun n C (s2231_px u v) = true := s2231_reach_up n C (s2231_px u v) C.output j hr hg
    have hne : u ≠ v := by
      intro e
      subst e
      rw [s2231_px_self] at hW
      have hf : true = false := hW.symm.trans (h1 _)
      cases hf
    refine ⟨hne, ?_⟩
    by_contra hna
    have hf : true = false := hW.symm.trans (h2 u v hne hna)
    cases hf
  refine ⟨?_, fun u hu v hv => (hcross u hu v hv).2, ?_⟩
  · intro w hw0 hw1
    exact (hcross w hw0 w hw1).1 rfl
  · by_contra hcon
    push_neg at hcon
    obtain ⟨c0, c1⟩ := hcon
    obtain ⟨u, hu, u2, hu2, hne⟩ := Finset.one_lt_card.mp c0
    obtain ⟨v, hv, v2, hv2, hnv⟩ := Finset.one_lt_card.mp c1
    have hc := hNF u u2 hne
    rw [Finset.card_le_one] at hc
    exact hnv (hc v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcross u hu v hv).2,
      (hcross u2 hu2 v hv).2⟩) v2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hcross u hu v2 hv2).2, (hcross u2 hu2 v2 hv2).2⟩))

def s2231_cen (n : ℕ) (C : Circuit) (i : ℕ) : Finset (Fin n) :=
  if (PEqualNP.TopForm.side (n := n) C i 0).card ≤ 1 then PEqualNP.TopForm.side (n := n) C i 0
  else if (PEqualNP.TopForm.side (n := n) C i 1).card ≤ 1 then
    PEqualNP.TopForm.side (n := n) C i 1
  else ∅

lemma s2231_cen_card (n : ℕ) (C : Circuit) (i : ℕ) : (s2231_cen n C i).card ≤ 1 := by
  unfold s2231_cen
  split_ifs with h0 h1
  · exact h0
  · exact h1
  · simp

theorem s2231 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 → PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CleanedNonEdge.OrReaches n C C.output j → (∀ w : Fin n, w ∈ PEqualNP.TopForm.side (n := n) C j 0 → w ∉ PEqualNP.TopForm.side (n := n) C j 1) ∧ (∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 → ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → G.Adj u v) ∧ ((PEqualNP.TopForm.side (n := n) C j 0).card ≤ 1 ∨ (PEqualNP.TopForm.side (n := n) C j 1).card ≤ 1)) ∧ (∀ F : Finset ℕ, (∀ e ∈ (Finset.univ.filter (fun e1 : Fin n × Fin n => e1.1 < e1.2 ∧ G.Adj e1.1 e1.2 ∧ PEqualNP.ReadK.readsAtMost C n [e1.1.val, e1.2.val] 1 = true)), ∃ i ∈ F, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i ∧ ((e.1 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧ e.2 ∈ PEqualNP.TopForm.side (n := n) C i 1) ∨ (e.2 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧ e.1 ∈ PEqualNP.TopForm.side (n := n) C i 1))) → ∃ T : Finset (Fin n), T.card ≤ F.card ∧ ∀ e3 ∈ (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)), e3.1 ∈ T ∨ e3.2 ∈ T) := by
  intro n G _ C hNF hAO h1 h2
  have P1 := s2231_part1 n G C hNF hAO h1 h2
  refine ⟨P1, ?_⟩
  intro F hF
  refine ⟨F.biUnion (s2231_cen n C), ?_, ?_⟩
  · have hc1 : (F.biUnion (s2231_cen n C)).card ≤ F.sum (fun i => (s2231_cen n C i).card) :=
      Finset.card_biUnion_le
    have hc2 : F.sum (fun i => (s2231_cen n C i).card) ≤ F.sum (fun _ : ℕ => (1 : ℕ)) :=
      Finset.sum_le_sum (fun i _ => s2231_cen_card n C i)
    have hc3 : F.sum (fun _ : ℕ => (1 : ℕ)) = F.card := by simp
    exact le_trans hc1 (le_trans hc2 (le_of_eq hc3))
  · intro e he
    obtain ⟨i, hiF, hi, hop, hreach, hside⟩ := hF e he
    obtain ⟨_, _, hcard⟩ := P1 i hi hop hreach
    by_cases c0 : (PEqualNP.TopForm.side (n := n) C i 0).card ≤ 1
    · have hc : s2231_cen n C i = PEqualNP.TopForm.side (n := n) C i 0 := by
        unfold s2231_cen; rw [if_pos c0]
      rcases hside with ⟨h, _⟩ | ⟨h, _⟩
      · left; exact Finset.mem_biUnion.mpr ⟨i, hiF, by rw [hc]; exact h⟩
      · right; exact Finset.mem_biUnion.mpr ⟨i, hiF, by rw [hc]; exact h⟩
    · have c1 : (PEqualNP.TopForm.side (n := n) C i 1).card ≤ 1 := hcard.resolve_left c0
      have hc : s2231_cen n C i = PEqualNP.TopForm.side (n := n) C i 1 := by
        unfold s2231_cen; rw [if_neg c0, if_pos c1]
      rcases hside with ⟨_, h⟩ | ⟨_, h⟩
      · right; exact Finset.mem_biUnion.mpr ⟨i, hiF, by rw [hc]; exact h⟩
      · left; exact Finset.mem_biUnion.mpr ⟨i, hiF, by rw [hc]; exact h⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

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

theorem s2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
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

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge

def s2234_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2234_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2234_stepWire x := rfl

lemma s2234_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2234_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2234_stepWire]
    omega

lemma s2234_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2234_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2234_stepWire w g).length := by simp [s2234_stepWire]; omega
    rw [ih (s2234_stepWire w g) hlt]
    simp [s2234_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2234_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2234_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [s2234_wires_eq_foldl, s2234_foldl_stepWire_length, List.length_ofFn]

lemma s2234_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def s2234_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma s2234_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma s2234_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    s2234_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then s2234_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2234_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [s2234_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl s2234_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, s2234_foldl_stepWire_length, hpre_len]
  have hCj : s2234_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [s2234_W]
    rw [s2234_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [s2234_foldl_stepWire_getD_lt post (s2234_stepWire w0 gj) (n + k) (by simp [s2234_stepWire]; omega)]
    simp [s2234_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [s2234_W]
    rw [s2234_wires_eq_foldl, hgs, List.foldl_append]
    exact (s2234_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact s2234_getD_ge_length w0 i (by omega)

lemma s2234_W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    s2234_W n C x u = x ⟨u, hu⟩ := by
  simp only [s2234_W]
  rw [s2234_wires_eq_foldl, s2234_foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma s2234_orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma s2234_orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
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

lemma s2234_orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma s2234_orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact s2234_orStep_getD_lt n cs g k hk

lemma s2234_orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := s2234_split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [s2234_gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [s2234_orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, s2234_orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, s2234_orFold_getD_lt n post _ m (by omega)]
    exact s2234_orStep_getD_lt n _ gk m (by omega)
  have h3 := s2234_orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩


lemma s2234_qorSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  simp only [orSets]
  rw [s2234_orFold_length]
  simp

lemma s2234_qreach_iff (n : ℕ) (C : Circuit) (k g : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) g ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, w < n + k ∧ OrReaches n C w g) := by
  have e : n + k - n = k := by omega
  constructor
  · intro h
    have h2 := h.2
    rw [e] at h2
    rcases (s2234_orSets_mem_iff n C k g hk).1 h2 with h3 | ⟨hop, w, hw, hn, hlt, hx⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, hlt, hn, hx⟩
  · intro h
    refine ⟨by omega, ?_⟩
    rw [e]
    refine (s2234_orSets_mem_iff n C k g hk).2 ?_
    rcases h with h | ⟨hop, w, hw, hlt, hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hr.1, hlt, hr.2⟩

lemma s2234_qreach_bound (n : ℕ) (C : Circuit) (w g : ℕ) (h : OrReaches n C w g) :
    n ≤ w ∧ w - n < C.gates.length := by
  refine ⟨h.1, ?_⟩
  by_contra hc
  have h2 := h.2
  have hlen : (orSets n C).length ≤ w - n := by rw [s2234_qorSets_len]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen] at h2
  simp at h2

lemma s2234_qreach_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := (s2234_qreach_iff n C k k hk).2 (Or.inl rfl)

lemma s2234_qreach_le (n : ℕ) (C : Circuit) (g : ℕ) : ∀ w : ℕ, OrReaches n C w g → n + g ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    obtain ⟨h1, h2⟩ := s2234_qreach_bound n C w g h
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases (s2234_qreach_iff n C k g hk).1 h with h3 | ⟨_, w', _, hlt, hr⟩
    · omega
    · have := ih w' hlt hr
      omega

lemma s2234_qreach_trans (n : ℕ) (C : Circuit) (i g : ℕ) (hg : OrReaches n C (n + i) g) :
    ∀ w : ℕ, OrReaches n C w i → OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    obtain ⟨h1, h2⟩ := s2234_qreach_bound n C w i h
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases (s2234_qreach_iff n C k i hk).1 h with h3 | ⟨hop, w', hw', hlt, hr⟩
    · rw [← h3]; exact hg
    · exact (s2234_qreach_iff n C k g hk).2 (Or.inr ⟨hop, w', hw', hlt, ih w' hlt hr⟩)

lemma s2234_qmem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (b : Fin n) :
    b ∈ PEqualNP.TopForm.orIn n C w ↔ ((b : ℕ) = w ∨ ∃ k, k < C.gates.length ∧
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (b : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma s2234_qorIn_eq_self (n : ℕ) (C : Circuit) (w : ℕ)
    (hw : ¬ (n ≤ w ∧ w - n < C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or)) :
    ∀ b ∈ PEqualNP.TopForm.orIn n C w, (b : ℕ) = w := by
  intro b hb
  rcases (s2234_qmem_orIn n C w b).1 hb with h | ⟨k', hk', hr, hop', hi⟩
  · exact h
  · exfalso
    obtain ⟨h1, h2⟩ := s2234_qreach_bound n C w k' hr
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have e : n + k - n = k := by omega
    rw [e] at hw h2
    rcases (s2234_qreach_iff n C k k' h2).1 hr with h | ⟨hop, _⟩
    · rw [h] at hop'
      exact hw ⟨h1, h2, hop'⟩
    · exact hw ⟨h1, h2, hop⟩

lemma s2234_qorIn_small (n : ℕ) (C : Circuit) (w : ℕ)
    (hw : ¬ (n ≤ w ∧ w - n < C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or)) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  have h1 := s2234_qorIn_eq_self n C w hw a ha
  have h2 := s2234_qorIn_eq_self n C w hw b hb
  exact Fin.ext (by omega)

lemma s2234_qorIn_or (n : ℕ) (C : Circuit) (k a b : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    PEqualNP.TopForm.orIn n C (n + k) =
      PEqualNP.TopForm.orIn n C a ∪ PEqualNP.TopForm.orIn n C b := by
  have hma : a ∈ (gateAt C k).inputs := by rw [hin]; simp
  have hmb : b ∈ (gateAt C k).inputs := by rw [hin]; simp
  ext i
  rw [Finset.mem_union, s2234_qmem_orIn, s2234_qmem_orIn, s2234_qmem_orIn]
  constructor
  · rintro (h | ⟨k', hk', hr, hop', hi⟩)
    · exfalso
      have := i.2
      omega
    · rcases (s2234_qreach_iff n C k k' hk).1 hr with h | ⟨_, w, hw, hwlt, hr'⟩
      · rw [h, hin, List.mem_cons, List.mem_singleton] at hi
        rcases hi with h4 | h4
        · exact Or.inl (Or.inl h4)
        · exact Or.inr (Or.inl h4)
      · rw [hin, List.mem_cons, List.mem_singleton] at hw
        rcases hw with h4 | h4
        · rw [h4] at hr'
          exact Or.inl (Or.inr ⟨k', hk', hr', hop', hi⟩)
        · rw [h4] at hr'
          exact Or.inr (Or.inr ⟨k', hk', hr', hop', hi⟩)
  · rintro ((h | ⟨k', hk', hr, hop', hi⟩) | (h | ⟨k', hk', hr, hop', hi⟩))
    · exact Or.inr ⟨k, hk, s2234_qreach_self n C k hk, hop, by rw [h]; exact hma⟩
    · exact Or.inr ⟨k', hk', (s2234_qreach_iff n C k k' hk).2 (Or.inr ⟨hop, a, hma, ha, hr⟩), hop', hi⟩
    · exact Or.inr ⟨k, hk, s2234_qreach_self n C k hk, hop, by rw [h]; exact hmb⟩
    · exact Or.inr ⟨k', hk', (s2234_qreach_iff n C k k' hk).2 (Or.inr ⟨hop, b, hmb, hb, hr⟩), hop', hi⟩

lemma s2234_qorIn_sub (n : ℕ) (C : Circuit) (i w : ℕ) (hr : OrReaches n C w i) :
    PEqualNP.TopForm.orIn n C (n + i) ⊆ PEqualNP.TopForm.orIn n C w := by
  intro b hb
  rcases (s2234_qmem_orIn n C (n + i) b).1 hb with h | ⟨k, hk, hr', hop, hi⟩
  · exfalso
    have := b.2
    omega
  · exact (s2234_qmem_orIn n C w b).2 (Or.inr ⟨k, hk, s2234_qreach_trans n C i k hr' w hr, hop, hi⟩)

lemma s2234_qval_reach (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : s2234_W n C x (n + g) = true) :
    ∀ w : ℕ, OrReaches n C w g → s2234_W n C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    obtain ⟨h1, h2⟩ := s2234_qreach_bound n C w g h
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases (s2234_qreach_iff n C k g hk).1 h with h3 | ⟨hop, w', hw', hlt, hr⟩
    · rw [← h3]; exact hv
    · rw [s2234_W_gate n C x k hk, hop]
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
      exact ⟨w', hw', by simp only [hlt, ite_true]; exact ih w' hlt hr⟩

lemma s2234_qval_orIn (n : ℕ) (C : Circuit) (w : ℕ) (b : Fin n)
    (hb : b ∈ PEqualNP.TopForm.orIn n C w) :
    s2234_W n C (fun r : Fin n => decide (r = b)) w = true := by
  rcases (s2234_qmem_orIn n C w b).1 hb with h | ⟨k, hk, hr, hop, hi⟩
  · rw [← h, s2234_W_input n C _ (b : ℕ) b.2]
    simp
  · refine s2234_qval_reach n C _ k ?_ w hr
    rw [s2234_W_gate n C _ k hk, hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
    have hlt : (b : ℕ) < n + k := by
      have := b.2
      omega
    refine ⟨(b : ℕ), hi, ?_⟩
    simp only [hlt, ite_true]
    rw [s2234_W_input n C _ (b : ℕ) b.2]
    simp

lemma s2234_qpart1 (n : ℕ) (C : Circuit)
    (h0 : ∀ a1 : Fin n, circuitFun n C (fun k1 => decide (k1 = a1)) = false)
    (i : ℕ) (hcard : 2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card) :
    ¬ OrReaches n C C.output i := by
  intro hr
  have hpos : 0 < (PEqualNP.TopForm.orIn n C (n + i)).card := by omega
  obtain ⟨b, hb⟩ := Finset.card_pos.1 hpos
  have h1 := s2234_qval_orIn n C (n + i) b hb
  have h2 := s2234_qval_reach n C _ i h1 C.output hr
  have h3 : s2234_W n C (fun r : Fin n => decide (r = b)) C.output = false := h0 b
  rw [h2] at h3
  cases h3

noncomputable def s2234_srv (n : ℕ) (C : Circuit) (R : Finset ℕ) : Finset ℕ :=
  @Finset.filter ℕ (fun i => (gateAt C i).op = GateOp.or ∧
    2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card ∧ ∃ w ∈ R, OrReaches n C w i)
    (fun _ => Classical.propDecidable _) (Finset.range C.gates.length)

lemma s2234_qmem_srv (n : ℕ) (C : Circuit) (R : Finset ℕ) (i : ℕ) :
    i ∈ s2234_srv n C R ↔ (i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card ∧ ∃ w ∈ R, OrReaches n C w i) := by
  unfold s2234_srv
  rw [@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _), Finset.mem_range]

lemma s2234_qsrv_mono (n : ℕ) (C : Circuit) (R R' : Finset ℕ) (h : R ⊆ R') :
    s2234_srv n C R ⊆ s2234_srv n C R' := by
  intro i hi
  obtain ⟨h1, h2, h3, w, hw, hr⟩ := (s2234_qmem_srv n C R i).1 hi
  exact (s2234_qmem_srv n C R' i).2 ⟨h1, h2, h3, w, h hw, hr⟩

lemma s2234_qcount (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hlen2 : ∀ g ∈ C.gates, g.inputs.length = 2) :
    ∀ (m : ℕ) (R : Finset ℕ), (∀ w ∈ R, w < m) →
      (R.biUnion (PEqualNP.TopForm.orIn n C)).card ≤ (s2234_srv n C R).card + R.card := by
  intro m
  induction m with
  | zero =>
    intro R hR
    have hRe : R = ∅ := Finset.eq_empty_of_forall_notMem (fun w hw => by
      have := hR w hw
      omega)
    subst hRe
    simp
  | succ m ih =>
    intro R hR
    by_cases hm : m ∈ R
    · have hR0 : ∀ w ∈ R.erase m, w < m := by
        intro w hw
        have h1 := Finset.ne_of_mem_erase hw
        have h2 := hR w (Finset.mem_of_mem_erase hw)
        omega
      have hins : insert m (R.erase m) = R := Finset.insert_erase hm
      have hcardR : (R.erase m).card + 1 = R.card := Finset.card_erase_add_one hm
      have hU : R.biUnion (PEqualNP.TopForm.orIn n C) =
          PEqualNP.TopForm.orIn n C m ∪ (R.erase m).biUnion (PEqualNP.TopForm.orIn n C) := by
        rw [← Finset.biUnion_insert (a := m) (s := R.erase m)
          (t := PEqualNP.TopForm.orIn n C), hins]
      by_cases hs : n ≤ m ∧ m - n < C.gates.length ∧ (gateAt C (m - n)).op = GateOp.or ∧
          2 ≤ (PEqualNP.TopForm.orIn n C m).card
      · obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
        obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
        have e : n + k - n = k := by omega
        rw [e] at hs2 hs3
        have hmem : gateAt C k ∈ C.gates := by
          rw [s2234_gateAt_eq C k hs2]
          exact List.getElem_mem hs2
        have hl := hlen2 _ hmem
        obtain ⟨a, b, hin⟩ : ∃ a b, (gateAt C k).inputs = [a, b] := List.length_eq_two.1 hl
        have hma : a ∈ (gateAt C k).inputs := by rw [hin]; simp
        have hmb : b ∈ (gateAt C k).inputs := by rw [hin]; simp
        have ha : a < n + k := hRB k hs2 a hma
        have hb : b < n + k := hRB k hs2 b hmb
        have hor := s2234_qorIn_or n C k a b hs2 hs3 hin ha hb
        have hR' : ∀ w ∈ insert a (insert b (R.erase (n + k))), w < n + k := by
          intro w hw
          rw [Finset.mem_insert, Finset.mem_insert] at hw
          rcases hw with h | h | h
          · omega
          · omega
          · exact hR0 w h
        have hih := ih _ hR'
        have hU' : (insert a (insert b (R.erase (n + k)))).biUnion (PEqualNP.TopForm.orIn n C) =
            R.biUnion (PEqualNP.TopForm.orIn n C) := by
          rw [hU, Finset.biUnion_insert, Finset.biUnion_insert, hor, Finset.union_assoc]
        have hc' : (insert a (insert b (R.erase (n + k)))).card ≤ (R.erase (n + k)).card + 2 := by
          have h1 := Finset.card_insert_le a (insert b (R.erase (n + k)))
          have h2 := Finset.card_insert_le b (R.erase (n + k))
          omega
        have hsub : s2234_srv n C (insert a (insert b (R.erase (n + k)))) ⊆ (s2234_srv n C R).erase k := by
          intro i hi
          obtain ⟨h1, h2, h3, w, hw, hr⟩ := (s2234_qmem_srv n C _ i).1 hi
          have hle := s2234_qreach_le n C i w hr
          have hwlt := hR' w hw
          rw [Finset.mem_erase]
          refine ⟨by omega, (s2234_qmem_srv n C R i).2 ⟨h1, h2, h3, ?_⟩⟩
          rw [Finset.mem_insert, Finset.mem_insert] at hw
          rcases hw with h | h | h
          · rw [h] at hr
            exact ⟨n + k, hm, (s2234_qreach_iff n C k i hs2).2 (Or.inr ⟨hs3, a, hma, ha, hr⟩)⟩
          · rw [h] at hr
            exact ⟨n + k, hm, (s2234_qreach_iff n C k i hs2).2 (Or.inr ⟨hs3, b, hmb, hb, hr⟩)⟩
          · exact ⟨w, Finset.mem_of_mem_erase h, hr⟩
        have hkmem : k ∈ s2234_srv n C R :=
          (s2234_qmem_srv n C R k).2 ⟨hs2, hs3, hs4, n + k, hm, s2234_qreach_self n C k hs2⟩
        have hc2 : ((s2234_srv n C R).erase k).card + 1 = (s2234_srv n C R).card :=
          Finset.card_erase_add_one hkmem
        have hc3 := Finset.card_le_card hsub
        rw [hU'] at hih
        omega
      · have hsmall : (PEqualNP.TopForm.orIn n C m).card ≤ 1 := by
          by_cases hs' : n ≤ m ∧ m - n < C.gates.length ∧ (gateAt C (m - n)).op = GateOp.or
          · by_contra hc
            exact hs ⟨hs'.1, hs'.2.1, hs'.2.2, by omega⟩
          · exact s2234_qorIn_small n C m hs'
        have hih := ih _ hR0
        have hmono := Finset.card_le_card (s2234_qsrv_mono n C _ _ (Finset.erase_subset m R))
        have hun := Finset.card_union_le (PEqualNP.TopForm.orIn n C m)
          ((R.erase m).biUnion (PEqualNP.TopForm.orIn n C))
        rw [hU]
        omega
    · refine ih R (fun w hw => ?_)
      have h1 := hR w hw
      have h2 : w ≠ m := fun h => hm (h ▸ hw)
      omega

lemma s2234_qfinal (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (F : Finset ℕ)
    (ctr : ℕ → Fin n) (lf : ℕ → ℕ)
    (hG : PEqualNP.TopForm.NoFourCycle G) (hRB : ReadsBack n C)
    (hlen2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hadj : ∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b) :
    ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} + F.card := by
  have key : ∀ (S : Set ℕ) (A B : ℕ), (∀ i, i ∈ S ↔ i ∈ s2234_srv n C (F.image lf)) →
      A ≤ (s2234_srv n C (F.image lf)).card + B → A ≤ S.ncard + B := by
    intro S A B hS hA
    have hSe : S = ((s2234_srv n C (F.image lf) : Finset ℕ) : Set ℕ) := by
      ext i
      exact (hS i).trans Finset.mem_coe.symm
    rw [hSe, Set.ncard_coe_finset]
    exact hA
  refine key _ _ _ ?_ ?_
  · intro i
    rw [Set.mem_ofPred_eq, s2234_qmem_srv]
    constructor
    · rintro ⟨h1, h2, h3, j, hj, hr⟩
      exact ⟨h1, h2, h3, lf j, Finset.mem_image_of_mem lf hj, hr⟩
    · rintro ⟨h1, h2, h3, w, hw, hr⟩
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
      exact ⟨h1, h2, h3, j, hj, hr⟩
  · have hpt : ∀ c : Fin n, ∀ X : Finset (Fin n),
        (∀ b, b ∈ X ↔ ∃ j ∈ F, ctr j = c ∧ b ∈ PEqualNP.TopForm.orIn n C (lf j)) →
        X.card ≤ (s2234_srv n C ((F.filter (fun j => ctr j = c)).image lf)).card +
          (F.filter (fun j => ctr j = c)).card := by
      intro c X hX
      have hXe : X = ((F.filter (fun j => ctr j = c)).image lf).biUnion
          (PEqualNP.TopForm.orIn n C) := by
        ext b
        rw [hX b, Finset.mem_biUnion]
        constructor
        · rintro ⟨j, hj, hc, hb⟩
          exact ⟨lf j, Finset.mem_image_of_mem lf (Finset.mem_filter.2 ⟨hj, hc⟩), hb⟩
        · rintro ⟨w, hw, hb⟩
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
          obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
          exact ⟨j, hj1, hj2, hb⟩
      have hc := s2234_qcount n C hRB hlen2
        (((F.filter (fun j => ctr j = c)).image lf).sup id + 1)
        ((F.filter (fun j => ctr j = c)).image lf)
        (fun w hw => Nat.lt_succ_of_le (Finset.le_sup (f := id) hw))
      have hi := Finset.card_image_le (s := F.filter (fun j => ctr j = c)) (f := lf)
      rw [hXe]
      omega
    have hdisj : ∀ c c' : Fin n, c ≠ c' → ∀ i,
        i ∈ s2234_srv n C ((F.filter (fun j => ctr j = c)).image lf) →
        i ∈ s2234_srv n C ((F.filter (fun j => ctr j = c')).image lf) → False := by
      intro c c' hne i h1 h2
      obtain ⟨hi, hop, hcard, w, hw, hr⟩ := (s2234_qmem_srv n C _ i).1 h1
      obtain ⟨_, _, _, w', hw', hr'⟩ := (s2234_qmem_srv n C _ i).1 h2
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
      obtain ⟨j', hj', rfl⟩ := Finset.mem_image.1 hw'
      obtain ⟨hjF, hjc⟩ := Finset.mem_filter.1 hj
      obtain ⟨hjF', hjc'⟩ := Finset.mem_filter.1 hj'
      refine absurd (le_trans hcard (le_trans (Finset.card_le_card ?_) (hG c c' hne))) (by omega)
      intro b hb
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [← hjc]
        exact hadj j hjF b (s2234_qorIn_sub n C i (lf j) hr hb)
      · rw [← hjc']
        exact hadj j' hjF' b (s2234_qorIn_sub n C i (lf j') hr' hb)
    have hpd : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
        (fun c => s2234_srv n C ((F.filter (fun j => ctr j = c)).image lf)) := by
      intro c _ c' _ hne
      exact Finset.disjoint_left.2 (fun i h1 h2 => hdisj c c' hne i h1 h2)
    have hsum1 : ∑ c : Fin n, (s2234_srv n C ((F.filter (fun j => ctr j = c)).image lf)).card ≤
        (s2234_srv n C (F.image lf)).card := by
      rw [← Finset.card_biUnion hpd]
      apply Finset.card_le_card
      intro i hi
      obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.1 hi
      exact s2234_qsrv_mono n C _ _ (Finset.image_subset_image (Finset.filter_subset _ _)) hc
    have hsum2 : ∑ c : Fin n, (F.filter (fun j => ctr j = c)).card = F.card :=
      (Finset.card_eq_sum_card_fiberwise (f := ctr) (s := F) (t := Finset.univ)
        (by intro x _; simp)).symm
    have hpt2 : ∀ c ∈ (Finset.univ : Finset (Fin n)), (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤
        (s2234_srv n C ((F.filter (fun j => ctr j = c)).image lf)).card +
          (F.filter (fun j => ctr j = c)).card := fun c _ => hpt c _ (fun b => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    refine le_trans (Finset.sum_le_sum hpt2) ?_
    rw [Finset.sum_add_distrib]
    exact add_le_add hsum1 (le_of_eq hsum2)

theorem s2234 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b) → (∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or → 2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card → (∃ j1 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j1) i) → ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output i) ∧ ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} + F.card := by
  intro n G hdec C F ctr lf hG hAO h0 hadj
  refine ⟨?_, ?_⟩
  · intro i _ _ hcard _
    exact s2234_qpart1 n C h0 i hcard
  · exact s2234_qfinal n G C F ctr lf hG hAO.2.1 hAO.2.2 hadj

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.TopForm

theorem three_count (L : ℕ) (F : Finset ℕ) (A B : Set ℕ)
    (hF : ∀ j ∈ F, j < L) (hA : ∀ i ∈ A, i < L) (hB : ∀ i ∈ B, i < L)
    (hFA : ∀ j ∈ F, j ∉ A) (hFB : ∀ j ∈ F, j ∉ B) (hAB : ∀ i ∈ A, i ∉ B) :
    F.card + A.ncard + B.ncard ≤ L := by
  classical
  have hAf : A.Finite := (Set.finite_lt_nat L).subset (fun i hi => hA i hi)
  have hBf : B.Finite := (Set.finite_lt_nat L).subset (fun i hi => hB i hi)
  rw [Set.ncard_eq_toFinset_card A hAf, Set.ncard_eq_toFinset_card B hBf]
  have h1 : Disjoint F hAf.toFinset := by
    rw [Finset.disjoint_left]
    intro j hj hj2
    exact hFA j hj ((Set.Finite.mem_toFinset hAf).mp hj2)
  have h2 : Disjoint (F ∪ hAf.toFinset) hBf.toFinset := by
    rw [Finset.disjoint_left]
    intro j hj hj2
    have hjB := (Set.Finite.mem_toFinset hBf).mp hj2
    rcases Finset.mem_union.mp hj with h | h
    · exact hFB j h hjB
    · exact hAB j ((Set.Finite.mem_toFinset hAf).mp h) hjB
  have h3 : (F ∪ hAf.toFinset) ∪ hBf.toFinset ⊆ Finset.range L := by
    intro j hj
    rw [Finset.mem_range]
    rcases Finset.mem_union.mp hj with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact hF j h
      · exact hA j ((Set.Finite.mem_toFinset hAf).mp h)
    · exact hB j ((Set.Finite.mem_toFinset hBf).mp h)
  have h4 := Finset.card_le_card h3
  rw [Finset.card_union_of_disjoint h2, Finset.card_union_of_disjoint h1, Finset.card_range] at h4
  exact h4

theorem sum_card_ge {n : ℕ} (E : Finset (Fin n × Fin n)) (U : Fin n → Finset (Fin n))
    (hlt : ∀ e ∈ E, e.1 < e.2) (h : ∀ e ∈ E, e.2 ∈ U e.1 ∨ e.1 ∈ U e.2) :
    E.card ≤ ∑ c : Fin n, (U c).card := by
  classical
  have hs := Finset.card_sigma (Finset.univ : Finset (Fin n)) U
  rw [← hs]
  have key1 : ∀ e ∈ E, (if e.2 ∈ U e.1 then (⟨e.1, e.2⟩ : Σ _ : Fin n, Fin n) else ⟨e.2, e.1⟩)
      ∈ (Finset.univ : Finset (Fin n)).sigma U := by
    intro e he
    by_cases hc : e.2 ∈ U e.1
    · rw [if_pos hc]
      exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hc⟩
    · rw [if_neg hc]
      rcases h e he with h1 | h1
      · exact absurd h1 hc
      · exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, h1⟩
  have key2 : ∀ e e2 : Fin n × Fin n, e.1 < e.2 → e2.1 < e2.2 →
      (if e.2 ∈ U e.1 then (⟨e.1, e.2⟩ : Σ _ : Fin n, Fin n) else ⟨e.2, e.1⟩) =
      (if e2.2 ∈ U e2.1 then (⟨e2.1, e2.2⟩ : Σ _ : Fin n, Fin n) else ⟨e2.2, e2.1⟩) → e = e2 := by
    intro e e2 h1 h2 heq
    by_cases c1 : e.2 ∈ U e.1
    · by_cases c2 : e2.2 ∈ U e2.1
      · rw [if_pos c1, if_pos c2] at heq
        have ha : e.1 = e2.1 := congrArg Sigma.fst heq
        have hb : e.2 = e2.2 := congrArg (fun s : (Σ _ : Fin n, Fin n) => (s.2 : Fin n)) heq
        exact Prod.ext ha hb
      · rw [if_pos c1, if_neg c2] at heq
        have ha : e.1 = e2.2 := congrArg Sigma.fst heq
        have hb : e.2 = e2.1 := congrArg (fun s : (Σ _ : Fin n, Fin n) => (s.2 : Fin n)) heq
        rw [ha, hb] at h1
        exact absurd h1 (lt_asymm h2)
    · by_cases c2 : e2.2 ∈ U e2.1
      · rw [if_neg c1, if_pos c2] at heq
        have ha : e.2 = e2.1 := congrArg Sigma.fst heq
        have hb : e.1 = e2.2 := congrArg (fun s : (Σ _ : Fin n, Fin n) => (s.2 : Fin n)) heq
        rw [ha, hb] at h1
        exact absurd h1 (lt_asymm h2)
      · rw [if_neg c1, if_neg c2] at heq
        have ha : e.2 = e2.2 := congrArg Sigma.fst heq
        have hb : e.1 = e2.1 := congrArg (fun s : (Σ _ : Fin n, Fin n) => (s.2 : Fin n)) heq
        exact Prod.ext hb ha
  refine Finset.card_le_card_of_injOn
    (fun e => if e.2 ∈ U e.1 then (⟨e.1, e.2⟩ : Σ _ : Fin n, Fin n) else ⟨e.2, e.1⟩) ?_ ?_
  · intro e he
    exact key1 e he
  · intro e he e2 he2 heq
    exact key2 e e2 (hlt e he) (hlt e2 he2) heq

theorem core (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (E : Finset (Fin n × Fin n))
    (hlt : ∀ e ∈ E, e.1 < e.2)
    (h30 : ∀ e ∈ E, ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j ∧
      ((e.1 ∈ side (n := n) C j 0 ∧ e.2 ∈ side (n := n) C j 1) ∨
        (e.2 ∈ side (n := n) C j 0 ∧ e.1 ∈ side (n := n) C j 1)))
    (h31a : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → OrReaches n C C.output j →
      (∀ w : Fin n, w ∈ side (n := n) C j 0 → w ∉ side (n := n) C j 1) ∧
      (∀ u : Fin n, u ∈ side (n := n) C j 0 → ∀ v : Fin n, v ∈ side (n := n) C j 1 → G.Adj u v) ∧
      ((side (n := n) C j 0).card ≤ 1 ∨ (side (n := n) C j 1).card ≤ 1))
    (h31b : ∀ F : Finset ℕ, (∀ e ∈ E, ∃ i ∈ F, i < C.gates.length ∧
        (gateAt C i).op = GateOp.and ∧ OrReaches n C C.output i ∧
        ((e.1 ∈ side (n := n) C i 0 ∧ e.2 ∈ side (n := n) C i 1) ∨
          (e.2 ∈ side (n := n) C i 0 ∧ e.1 ∈ side (n := n) C i 1))) →
      ∃ T : Finset (Fin n), T.card ≤ F.card ∧ ∀ e3 ∈ E, e3.1 ∈ T ∨ e3.2 ∈ T)
    (h33 : ∀ F : Finset ℕ, (∀ j ∈ F, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
        OrReaches n C C.output j) →
      F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
        OrReaches n C C.output i} + 1)
    (h34 : ∀ (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ),
      (∀ j ∈ F, ∀ b : Fin n, b ∈ orIn n C (lf j) → G.Adj (ctr j) b) →
      (∀ i < C.gates.length, (gateAt C i).op = GateOp.or → 2 ≤ (orIn n C (n + i)).card →
        (∃ j1 ∈ F, OrReaches n C (lf j1) i) → ¬ OrReaches n C C.output i) ∧
      ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n =>
        ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ orIn n C (lf j2))).card ≤
        Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (gateAt C i2).op = GateOp.or ∧
          2 ≤ (orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, OrReaches n C (lf j3) i2} + F.card) :
    ∃ T : Finset (Fin n), (∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T) ∧ E.card + T.card ≤ C.size + 1 := by
  classical
  by_cases hE : E = ∅
  · subst hE
    refine ⟨∅, ?_, ?_⟩
    · intro e he
      simp at he
    · rw [Finset.card_empty, Finset.card_empty]
      exact Nat.zero_le _
  obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.mpr hE
  obtain ⟨F, hF⟩ : ∃ F : Finset ℕ, ∀ j, j ∈ F ↔ (j < C.gates.length ∧
      (gateAt C j).op = GateOp.and ∧ OrReaches n C C.output j ∧
      (side (n := n) C j 0).Nonempty ∧ (side (n := n) C j 1).Nonempty) :=
    ⟨(Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j ∧
      (side (n := n) C j 0).Nonempty ∧ (side (n := n) C j 1).Nonempty),
      fun j => by rw [Finset.mem_filter, Finset.mem_range]⟩
  have hper : ∀ j : ℕ, ∃ (c : Fin n) (l : ℕ), j ∈ F →
      (∀ b : Fin n, b ∈ orIn n C l → G.Adj c b) ∧
      (∀ u : Fin n, u ∈ side (n := n) C j 0 → ∀ v : Fin n, v ∈ side (n := n) C j 1 →
        (c = u ∧ v ∈ orIn n C l) ∨ (c = v ∧ u ∈ orIn n C l)) := by
    intro j
    by_cases hj : j ∈ F
    · obtain ⟨hjl, hand, hor, hn0, hn1⟩ := (hF j).mp hj
      obtain ⟨hdis, hadj, hcard⟩ := h31a j hjl hand hor
      rcases hcard with hc | hc
      · obtain ⟨c, hc0⟩ := hn0
        refine ⟨c, opnd C j 1, fun _ => ⟨?_, ?_⟩⟩
        · intro b hb
          exact hadj c hc0 b hb
        · intro u hu v hv
          exact Or.inl ⟨Finset.card_le_one.mp hc c hc0 u hu, hv⟩
      · obtain ⟨c, hc1⟩ := hn1
        refine ⟨c, opnd C j 0, fun _ => ⟨?_, ?_⟩⟩
        · intro b hb
          exact (hadj b hb c hc1).symm
        · intro u hu v hv
          exact Or.inr ⟨Finset.card_le_one.mp hc c hc1 v hv, hu⟩
    · exact ⟨e0.1, 0, fun h => absurd h hj⟩
  choose ctr lf hcl using hper
  have hw : ∀ e ∈ E, ∃ i ∈ F, i < C.gates.length ∧
      (gateAt C i).op = GateOp.and ∧ OrReaches n C C.output i ∧
      ((e.1 ∈ side (n := n) C i 0 ∧ e.2 ∈ side (n := n) C i 1) ∨
        (e.2 ∈ side (n := n) C i 0 ∧ e.1 ∈ side (n := n) C i 1)) := by
    intro e he
    obtain ⟨j, hjl, hand, hor, hs⟩ := h30 e he
    refine ⟨j, (hF j).mpr ⟨hjl, hand, hor, ?_, ?_⟩, hjl, hand, hor, hs⟩
    · rcases hs with hs | hs
      · exact ⟨e.1, hs.1⟩
      · exact ⟨e.2, hs.1⟩
    · rcases hs with hs | hs
      · exact ⟨e.2, hs.2⟩
      · exact ⟨e.1, hs.2⟩
  obtain ⟨T, hTc, hTcov⟩ := h31b F hw
  have hFand : ∀ j ∈ F, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j := by
    intro j hj
    obtain ⟨ha, hb, hc, _⟩ := (hF j).mp hj
    exact ⟨ha, hb, hc⟩
  have h3 := h33 F hFand
  obtain ⟨h4a, h4b⟩ := h34 F ctr lf (fun j hj => (hcl j hj).1)
  have hEsum := le_trans (sum_card_ge E (fun c => Finset.univ.filter (fun b2 : Fin n =>
      ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ orIn n C (lf j2))) hlt (by
    intro e he
    obtain ⟨j, hjF, _, _, _, hs⟩ := hw e he
    rcases hs with hs | hs
    · rcases (hcl j hjF).2 e.1 hs.1 e.2 hs.2 with h | h
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩)
    · rcases (hcl j hjF).2 e.2 hs.1 e.1 hs.2 with h | h
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩)
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩))) h4b
  have hcount := three_count C.gates.length F
    {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i}
    {i2 : ℕ | i2 < C.gates.length ∧ (gateAt C i2).op = GateOp.or ∧
      2 ≤ (orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, OrReaches n C (lf j3) i2}
    (fun j hj => (hFand j hj).1) (fun i hi => hi.1) (fun i hi => hi.1)
    (fun j hj hjA => by
      have h1 := (hFand j hj).2.1
      have h2 : (gateAt C j).op = GateOp.or := hjA.2.1
      rw [h2] at h1
      cases h1)
    (fun j hj hjB => by
      have h1 := (hFand j hj).2.1
      have h2 : (gateAt C j).op = GateOp.or := hjB.2.1
      rw [h2] at h1
      cases h1)
    (fun i hi hiB => h4a i hi.1 hi.2.1 hiB.2.2.1 hiB.2.2.2 hi.2.2)
  refine ⟨T, hTcov, ?_⟩
  have hsz : C.size = C.gates.length := rfl
  rw [hsz]
  omega

theorem S35_main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 → PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false) → ∃ T : Finset (Fin n), (∀ e ∈ (Finset.univ.filter (fun e1 : Fin n × Fin n => e1.1 < e1.2 ∧ G.Adj e1.1 e1.2 ∧ PEqualNP.ReadK.readsAtMost C n [e1.1.val, e1.2.val] 1 = true)), e.1 ∈ T ∨ e.2 ∈ T) ∧ (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)).card + T.card ≤ C.size + 1 := by
  intro n G _ C h4 hA h1 h2
  have h31 := s2231 n G C h4 hA h1 h2
  exact core n G C _ (fun e he => (Finset.mem_filter.mp he).2.1)
    (fun e he => s2230 n C e.1 e.2 hA h1 (Finset.mem_filter.mp he).2.1
      (Finset.mem_filter.mp he).2.2.2)
    h31.1 h31.2 (fun F => s2233 n C F hA) (fun F ctr lf => s2234 n G C F ctr lf h4 hA h1)

theorem cor_setList_pair {n : ℕ} (a b : Fin n) (hab : a < b) :
    PEqualNP.ReadK.setList ({a, b} : Finset (Fin n)) = [a.val, b.val] := by
  have key : ∀ x y : Fin n, x < y → y < x → x = y :=
    fun x y h1 h2 => absurd h1 (lt_asymm h2)
  have hp1 : List.Pairwise (fun x y : Fin n => x < y)
      ((List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n))))) :=
    List.Pairwise.filter _ (List.pairwise_lt_finRange n)
  have hp2 : List.Pairwise (fun x y : Fin n => x < y) [a, b] := by
    simp [hab]
  have hperm : List.Perm
      ((List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n))))) [a, b] := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact List.Nodup.filter _ (List.nodup_finRange n)
    · simp [ne_of_lt hab]
    · ext x
      simp
  have h : (List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n)))) = [a, b] :=
    List.Perm.eq_of_pairwise (fun x y _ _ => key x y) hp1 hp2 hperm
  unfold PEqualNP.ReadK.setList
  rw [h]
  rfl

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → PEqualNP.ReadK.IsReadK n C 1 → ∃ T : Finset (Fin n), (∀ u2 v2 : Fin n, G.Adj u2 v2 → u2 ∈ T ∨ v2 ∈ T) ∧ G.edgeFinset.card + T.card ≤ C.size + 1 := by
  intro n G _ C h4 hAO hfun hread
  have hw1 : ∀ a1 : Fin n,
      PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false := by
    intro a1
    rw [hfun, decide_eq_false_iff_not]
    rintro ⟨u, v, huv, hu, hv⟩
    have hu1 : u = a1 := by simpa using hu
    have hv1 : v = a1 := by simpa using hv
    exact huv.ne (hu1.trans hv1.symm)
  have hw2 : ∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 →
      PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false := by
    intro a2 b2 hne hna
    rw [hfun, decide_eq_false_iff_not]
    rintro ⟨u, v, huv, hu, hv⟩
    have hu1 : u = a2 ∨ u = b2 := by simpa using hu
    have hv1 : v = a2 ∨ v = b2 := by simpa using hv
    rcases hu1 with h1 | h1 <;> rcases hv1 with h2 | h2
    · exact huv.ne (h1.trans h2.symm)
    · rw [h1, h2] at huv
      exact hna huv
    · rw [h1, h2] at huv
      exact hna huv.symm
    · exact huv.ne (h1.trans h2.symm)
  have hrd : ∀ a b : Fin n, a < b → G.Adj a b →
      PEqualNP.ReadK.readsAtMost C n [a.val, b.val] 1 = true := by
    intro a b hab hadj
    have hpi : PEqualNP.ReadK.IsPrimeImplicant n C ({a, b} : Finset (Fin n)) := by
      constructor
      · rw [hfun, decide_eq_true_eq]
        exact ⟨a, b, hadj, by simp [PEqualNP.ReadK.setInput], by simp [PEqualNP.ReadK.setInput]⟩
      · intro T hT
        rw [hfun, decide_eq_false_iff_not]
        rintro ⟨u, v, huv, hu, hv⟩
        have hu1 : u ∈ T := by simpa [PEqualNP.ReadK.setInput] using hu
        have hv1 : v ∈ T := by simpa [PEqualNP.ReadK.setInput] using hv
        obtain ⟨hsub, hnot⟩ := Finset.ssubset_def.mp (Finset.mem_ssubsets.mp hT)
        have hu2 := hsub hu1
        have hv2 := hsub hv1
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu2 hv2
        have hboth : a ∈ T ∧ b ∈ T := by
          rcases hu2 with h1 | h1 <;> rcases hv2 with h2 | h2
          · exact absurd (h1.trans h2.symm) huv.ne
          · rw [h1] at hu1
            rw [h2] at hv1
            exact ⟨hu1, hv1⟩
          · rw [h1] at hu1
            rw [h2] at hv1
            exact ⟨hv1, hu1⟩
          · exact absurd (h1.trans h2.symm) huv.ne
        apply hnot
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx
        · rw [hx]
          exact hboth.1
        · rw [hx]
          exact hboth.2
    have h1 := hread ({a, b} : Finset (Fin n)) hpi
    rw [cor_setList_pair a b hab] at h1
    exact h1
  obtain ⟨T, hT, hcard⟩ := S35_main_aux n G C h4 hAO hw1 hw2
  refine ⟨T, ?_, ?_⟩
  · intro u2 v2 huv
    rcases lt_trichotomy u2 v2 with hlt | heq | hgt
    · exact hT (u2, v2) (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hlt, huv, hrd u2 v2 hlt huv⟩)
    · exact absurd heq huv.ne
    · exact (hT (v2, u2) (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hgt, huv.symm, hrd v2 u2 hgt huv.symm⟩)).symm
  · have hsub : G.edgeFinset ⊆ (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)).image (fun e : Fin n × Fin n => Sym2.mk e.1 e.2) := by
      intro e he
      obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
      rw [SimpleGraph.mem_edgeFinset] at he
      have he2 : Sym2.mk u v ∈ G.edgeSet := he
      have huv : G.Adj u v := (SimpleGraph.mem_edgeSet G).mp he2
      rcases lt_trichotomy u v with hlt | heq | hgt
      · exact Finset.mem_image.mpr ⟨(u, v), Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hlt, huv, hrd u v hlt huv⟩, rfl⟩
      · exact absurd heq huv.ne
      · exact Finset.mem_image.mpr ⟨(v, u), Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hgt, huv.symm, hrd v u hgt huv.symm⟩, Sym2.eq_swap⟩
    have hle := (Finset.card_le_card hsub).trans Finset.card_image_le
    exact le_trans (Nat.add_le_add_right hle T.card) hcard

end PEqualNP.Outside.L_meta_2583.ReadLower.General

namespace PEqualNP.Outside.L_meta_2583.ReadLower

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

theorem noRectangle {m n : ℕ} (E : Finset (Fin m × Fin n))
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

theorem counts {m n : ℕ} (E : Finset (Fin m × Fin n)) :
    E.card ≤ (letI := Classical.decRel (graph E).Adj; (graph E).edgeFinset.card) := by
  classical
  apply Finset.card_le_card_of_injOn (fun p : Fin m × Fin n => Sym2.mk (Fin.castAdd n p.1) (Fin.natAdd m p.2))
  · intro p hp
    rw [Finset.mem_coe,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
    simpa [graph,cross] using hp
  · rintro ⟨a,b⟩ _ ⟨c,d⟩ _ eq
    rcases (Sym2.mk_eq_mk_iff (p := (Fin.castAdd n a, Fin.natAdd m b)) (q := (Fin.castAdd n c, Fin.natAdd m d))).mp eq with forward|reverse
    · have hf := congrArg Prod.fst forward
      have hs := congrArg Prod.snd forward
      exact Prod.ext (by simpa using hf) (by simpa using hs)
    · have h : Fin.castAdd n a = Fin.natAdd m d := congrArg Prod.fst reverse
      have h' := congrArg Fin.val h
      simp at h'
      omega

end PEqualNP.Outside.L_meta_2583.ReadLower

open PEqualNP.Outside.L_meta_2583.ReadLower in
theorem PEqualNP.Outside.L_meta_2583.ReadLower.cover_bound : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → PEqualNP.ReadK.IsReadK (x1 + x2) x4 (1 : ℕ) → ∃ (x9 : Finset (Fin x1)) (x10 : Finset (Fin x2)), (∀ x11 ∈ x3, x11.1 ∈ x9 ∨ x11.2 ∈ x10) ∧ x3.card + x9.card + x10.card ≤ x4.size + (1 : ℕ) := by
  classical
  intro m n E C rect ao computes readOne
  let G := graph E
  letI : DecidableRel G.Adj := Classical.decRel _
  have hfunc (x : Fin (m+n) → Bool) :
      PEqualNP.MetaComplexity.circuitFun (m+n) C x =
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := by
    rw [computes]
    congr 1
    apply propext
    constructor
    · rintro ⟨p,l,he,hp,hl⟩
      exact ⟨Fin.castAdd n p,Fin.natAdd m l,by simpa [G,graph,cross] using he,hp,hl⟩
    · rintro ⟨u,v,ha,hu,hv⟩
      cases u using Fin.addCases <;> cases v using Fin.addCases <;> simp [G,graph,cross] at ha
      · exact ⟨_,_,ha,hu,hv⟩
      · exact ⟨_,_,ha,hv,hu⟩
  obtain ⟨T,covers,bound⟩ := General.main_aux (m+n) G C (noRectangle E rect) ao hfunc readOne
  let S := T.map finSumFinEquiv.symm.toEmbedding
  refine ⟨S.toLeft,S.toRight,?_,?_⟩
  · rintro ⟨p,l⟩ h
    have hit := covers (Fin.castAdd n p) (Fin.natAdd m l) (by simpa [G,graph,cross] using h)
    rcases hit with hp|hl
    · left
      apply Finset.mem_toLeft.mpr
      exact Finset.mem_map.mpr ⟨_,hp,finSumFinEquiv_symm_apply_castAdd p⟩
    · right
      apply Finset.mem_toRight.mpr
      exact Finset.mem_map.mpr ⟨_,hl,finSumFinEquiv_symm_apply_natAdd l⟩
  · have eq : S.toLeft.card + S.toRight.card = T.card := Finset.card_toLeft_add_card_toRight.trans (Finset.card_map _)
    have le : E.card ≤ G.edgeFinset.card := counts E
    omega


namespace PEqualNP.Outside.L_meta_2583_aux.Geometry

theorem lines_through {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 1 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (huniq : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb)
    (p0 : Fin N) : (Finset.univ.filter (fun l => I p0 l)).card = q + 1 := by
  have h1 : ∀ p ∈ (Finset.univ : Finset (Fin N)).erase p0,
      ((Finset.univ.filter (fun l => I p0 l)).filter (fun l => I p l)).card = 1 := by
    intro p hp
    have hne : p0 ≠ p := (Finset.ne_of_mem_erase hp).symm
    obtain ⟨l, hl, hu⟩ := huniq p0 p hne
    rw [Finset.card_eq_one]
    refine ⟨l, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hx
      exact hu x hx
    · intro hx
      rw [hx]
      exact hl
  have h2 : ∀ l ∈ Finset.univ.filter (fun l => I p0 l),
      (((Finset.univ : Finset (Fin N)).erase p0).filter (fun p => I p l)).card = q := by
    intro l hl
    have hl' := (Finset.mem_filter.mp hl).2
    have e : ((Finset.univ : Finset (Fin N)).erase p0).filter (fun p => I p l)
        = (Finset.univ.filter (fun p => I p l)).erase p0 := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    have hmem : p0 ∈ Finset.univ.filter (fun p => I p l) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl'⟩
    rw [e, Finset.card_erase_of_mem hmem, hline l]
    rfl
  have h3 : ∑ p ∈ (Finset.univ : Finset (Fin N)).erase p0,
        ((Finset.univ.filter (fun l => I p0 l)).filter (fun l => I p l)).card
      = ∑ l ∈ Finset.univ.filter (fun l => I p0 l),
        (((Finset.univ : Finset (Fin N)).erase p0).filter (fun p => I p l)).card :=
by
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2] at h3
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ p0),
    Finset.card_univ, Fintype.card_fin] at h3
  have e : N - 1 = (q + 1) * q := by
    have : (q + 1) * q = q ^ 2 + q := by ring
    omega
  rw [e] at h3
  exact (Nat.eq_of_mul_eq_mul_right hq h3).symm

def Inc {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    Finset (Fin N × Fin N) := (A ×ˢ B).filter (fun pl => I pl.1 pl.2)

theorem Inc_right {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    (Inc I A B).card = ∑ l ∈ B, (A.filter (fun p => I p l)).card := by
  unfold Inc
  rw [Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.card_filter]

theorem Inc_left {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    (Inc I A B).card = ∑ p ∈ A, (B.filter (fun l => I p l)).card := by
  unfold Inc
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.card_filter]

def edges {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] :
    Finset (Fin N × Fin N) := Finset.univ.filter fun pl => I pl.1 pl.2

lemma inc_univ_eq_edges {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] :
    Inc I Finset.univ Finset.univ = edges I := by
  ext pl
  simp [Inc, edges]

lemma edge_count {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    (edges I).card = N * (q + 1) := by
  rw [← inc_univ_eq_edges, Inc_right]
  simp_rw [hline]
  simp

lemma no_rectangle {N : ℕ} (I : Fin N → Fin N → Prop)
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p p' l l' : Fin N) (hp : p ≠ p') (hl : l ≠ l') :
    ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l') := by
  rintro ⟨a, b, c, d⟩
  exact hl ((huniq p p' hp).unique ⟨a, c⟩ ⟨b, d⟩)

lemma cover_lower {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpoint : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (P L : Finset (Fin N))
    (hcover : ∀ p l : Fin N, I p l → p ∈ P ∨ l ∈ L) :
    N ≤ P.card + L.card := by
  have h0 : (Inc I Finset.univ Finset.univ).card = N * (q + 1) := by
    rw [inc_univ_eq_edges]
    exact edge_count I hline
  have h1 : (Inc I P Finset.univ).card = P.card * (q + 1) := by
    rw [Inc_left]
    simp_rw [hpoint]
    simp
  have h2 : (Inc I Finset.univ L).card = L.card * (q + 1) := by
    rw [Inc_right]
    simp_rw [hline]
    simp
  have hsub : Inc I Finset.univ Finset.univ ⊆
      Inc I P Finset.univ ∪ Inc I Finset.univ L := by
    intro pl hpl
    have hi : I pl.1 pl.2 := (Finset.mem_filter.mp hpl).2
    rcases hcover pl.1 pl.2 hi with hp | hl
    · exact Finset.mem_union_left _ (by simp [Inc, hp, hi])
    · exact Finset.mem_union_right _ (by simp [Inc, hl, hi])
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [h0, h1, h2, ← Nat.add_mul] at hc
  exact Nat.le_of_mul_le_mul_right hc (Nat.succ_pos q)

lemma hall_condition {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpoint : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (P : Finset (Fin N)) :
    P.card ≤ (Finset.univ.filter fun l => ∃ p ∈ P, I p l).card := by
  let L := Finset.univ.filter fun l => ∃ p ∈ P, I p l
  have h1 : (Inc I P Finset.univ).card = P.card * (q + 1) := by
    rw [Inc_left]
    simp_rw [hpoint]
    simp
  have h2 : (Inc I Finset.univ L).card = L.card * (q + 1) := by
    rw [Inc_right]
    simp_rw [hline]
    simp
  have hsub : Inc I P Finset.univ ⊆ Inc I Finset.univ L := by
    intro pl hpl
    have hp : pl.1 ∈ P := (Finset.mem_product.mp (Finset.mem_filter.mp hpl).1).1
    have hi : I pl.1 pl.2 := (Finset.mem_filter.mp hpl).2
    have hl : pl.2 ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_univ _, pl.1, hp, hi⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, hl⟩, hi⟩
  have hc := Finset.card_le_card hsub
  rw [h1, h2] at hc
  exact Nat.le_of_mul_le_mul_right hc (Nat.succ_pos q)

lemma plane_data {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    (∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1) ∧
    (edges I).card = N * (q + 1) ∧
    (∀ P L : Finset (Fin N), (∀ p l : Fin N, I p l → p ∈ P ∨ l ∈ L) →
      N ≤ P.card + L.card) := by
  have hp := lines_through q I (by omega) hN hline huniq
  exact ⟨hp, edge_count I hline, fun P L hc => cover_lower I hline hp P L hc⟩

end PEqualNP.Outside.L_meta_2583_aux.Geometry
