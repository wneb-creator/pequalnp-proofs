import PEqualNP.Defs
import Mathlib



-- General graph covering bound from the checked proof of L-meta-2237.
namespace PEqualNP.Outside.L_meta_2583.ReadOneCost.General


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

end PEqualNP.Outside.L_meta_2583.ReadOneCost.General

namespace PEqualNP.Outside.L_meta_2583.ReadOneCost

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

end PEqualNP.Outside.L_meta_2583.ReadOneCost

namespace PEqualNP.Outside.L_meta_2583.ReadOneCost

theorem cover_bound : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → PEqualNP.ReadK.IsReadK (x1 + x2) x4 (1 : ℕ) → ∃ (x9 : Finset (Fin x1)) (x10 : Finset (Fin x2)), (∀ x11 ∈ x3, x11.1 ∈ x9 ∨ x11.2 ∈ x10) ∧ x3.card + x9.card + x10.card ≤ x4.size + (1 : ℕ) := by
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

end PEqualNP.Outside.L_meta_2583.ReadOneCost


-- Plane incidence counting adapts the checked argument of L_meta_8805.
namespace PEqualNP.Outside.L_meta_2583.PlaneGeometry

theorem lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 0 < q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)

theorem cardL {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    ((A ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)).card
      = ∑ p ∈ A, (B.filter (fun w => I p w)).card := by
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.card_filter]

theorem cardR {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    ((A ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)).card
      = ∑ w ∈ B, (A.filter (fun p => I p w)).card := by
  rw [Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.card_filter]

theorem cover {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpt : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (A B : Finset (Fin N)) (hc : ∀ p w : Fin N, I p w → p ∈ A ∨ w ∈ B) :
    N ≤ A.card + B.card := by
  have hE : (((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = N * (q + 1) := by
    rw [cardR, Finset.sum_congr rfl (fun w _ => hl w), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have hA : ((A ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = A.card * (q + 1) := by
    rw [cardL, Finset.sum_congr rfl (fun p _ => hpt p), Finset.sum_const, smul_eq_mul]
  have hB : (((Finset.univ : Finset (Fin N)) ×ˢ B).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = B.card * (q + 1) := by
    rw [cardR, Finset.sum_congr rfl (fun w _ => hl w), Finset.sum_const, smul_eq_mul]
  have hsub : ((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)
      ⊆ ((A ×ˢ (Finset.univ : Finset (Fin N))).filter (fun pw : Fin N × Fin N => I pw.1 pw.2))
        ∪ (((Finset.univ : Finset (Fin N)) ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)) := by
    rintro ⟨p, w⟩ h
    have hI : I p w := (Finset.mem_filter.mp h).2
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product]
    rcases hc p w hI with h1 | h1
    · exact Or.inl ⟨⟨h1, Finset.mem_univ _⟩, hI⟩
    · exact Or.inr ⟨⟨Finset.mem_univ _, h1⟩, hI⟩
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [hE, hA, hB, ← Nat.add_mul] at h
  exact Nat.le_of_mul_le_mul_right h (Nat.succ_pos q)

def edges {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I] : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => I e.1 e.2)

lemma edges_card {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    (edges I).card = N * (q + 1) := by
  have count : (((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun e : Fin N × Fin N => I e.1 e.2)).card = N * (q + 1) := by
    rw [cardR, Finset.sum_congr rfl (fun l _ => hl l), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  simpa only [Finset.univ_product_univ, edges] using count

lemma no_rectangle {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p p' l l' : Fin N) (hp : p ≠ p') (hl : l ≠ l') :
    ¬ ((p, l) ∈ edges I ∧ (p, l') ∈ edges I ∧ (p', l) ∈ edges I ∧ (p', l') ∈ edges I) := by
  intro h
  have h1 : I p l := (Finset.mem_filter.mp h.1).2
  have h2 : I p l' := (Finset.mem_filter.mp h.2.1).2
  have h3 : I p' l := (Finset.mem_filter.mp h.2.2.1).2
  have h4 : I p' l' := (Finset.mem_filter.mp h.2.2.2).2
  exact hl ((hu p p' hp).unique ⟨h1, h3⟩ ⟨h2, h4⟩)

lemma cover_edges {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B : Finset (Fin N)) (hc : ∀ e ∈ edges I, e.1 ∈ A ∨ e.2 ∈ B) :
    N ≤ A.card + B.card := by
  apply cover q I hl (lines_through q N I hq hN hl hu) A B
  intro p l h
  exact hc (p, l) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

end PEqualNP.Outside.L_meta_2583.PlaneGeometry


namespace PEqualNP.Outside.L_meta_2583.StarConstruction

namespace A3692

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_stepW_len (gs : List Gate) (inp : List Bool) :
    (gs.foldl stepW inp).length = inp.length + gs.length := by
  induction gs generalizing inp with
  | nil => simp
  | cons g rest ih =>
    simp [List.foldl, stepW, ih]
    omega

private lemma wires_eq_foldl (C : Circuit) (inp : List Bool) :
    C.wires inp = C.gates.foldl stepW inp := rfl

private lemma wires_len (C : Circuit) (inp : List Bool) :
    (C.wires inp).length = inp.length + C.gates.length := by
  simpa [wires_eq_foldl] using foldl_stepW_len C.gates inp

private lemma getD_append_left (l1 l2 : List Bool) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_append_self (l1 : List Bool) (b : Bool) :
    (l1 ++ [b]).getD l1.length false = b := by
  simp [List.getD]

private lemma getD_of_ge (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD, List.getElem?_eq_none hi]

private lemma getD_ofFn {n : ℕ} (z : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn z).getD i false = z ⟨i, hi⟩ := by
  simp [List.getD, hi]

private def wireVal (n : ℕ) (gs : List Gate) (z : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl stepW (List.ofFn z)).getD i false

private lemma wireVal_append_gate_lt (n : ℕ) (gs : List Gate) (g : Gate) (z : Fin n → Bool)
    (i : ℕ) (hi : i < n + gs.length) :
    wireVal n (gs ++ [g]) z i = wireVal n gs z i := by
  unfold wireVal
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl stepW (List.ofFn z)).length = n + gs.length := by
    rw [foldl_stepW_len, List.length_ofFn]
  exact getD_append_left _ _ i (by omega)

private lemma wireVal_append_gate_self (n : ℕ) (gs : List Gate) (g : Gate) (z : Fin n → Bool) :
    wireVal n (gs ++ [g]) z (n + gs.length) =
      g.op.eval (g.inputs.map (fun i => wireVal n gs z i)) := by
  unfold wireVal
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl stepW (List.ofFn z)).length = n + gs.length := by
    rw [foldl_stepW_len, List.length_ofFn]
  rw [← hlen]
  exact getD_append_self (gs.foldl stepW (List.ofFn z)) _

private def gateAtL (gs : List Gate) (j : ℕ) : Gate :=
  gs.getD j ⟨GateOp.or, []⟩

private lemma gateAtL_append_lt (gs : List Gate) (g : Gate) (j : ℕ) (hj : j < gs.length) :
    gateAtL (gs ++ [g]) j = gateAtL gs j := by
  simp [gateAtL, List.getD, List.getElem?_append_left hj]

private lemma gateAtL_append_self (gs : List Gate) (g : Gate) :
    gateAtL (gs ++ [g]) gs.length = g := by
  simp [gateAtL, List.getD]

private def Good (x1 x2 : ℕ) (S : Bool → Finset ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gateAtL gs j).inputs, i < x1 + x2 + j) ∧
  (∀ b : Bool, ∀ w ∈ S b, w < x1 + x2 + gs.length) ∧
  (∀ b : Bool, ∀ w ∈ S b,
    (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
    ∃ j < gs.length, w = x1 + x2 + j ∧ (gateAtL gs j).op = GateOp.or ∧
      ∀ u ∈ (gateAtL gs j).inputs, u ∈ S b) ∧
  (∀ j < gs.length, (gateAtL gs j).op = GateOp.and →
    ∃ a c : ℕ, (gateAtL gs j).inputs = [a, c] ∧ a ∈ S false ∧ c ∈ S true)

private def S0 (x1 x2 : ℕ) (b : Bool) : Finset ℕ :=
  if b then Finset.Ico x1 (x1 + x2) else Finset.range x1

private lemma good_init (x1 x2 : ℕ) : Good x1 x2 (S0 x1 x2) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg; cases hg
  · intro j hj; simp at hj
  · intro b w hw
    cases b <;> simp [S0] at hw <;> omega
  · intro b w hw
    left
    cases b <;> simp [S0] at hw
    · exact ⟨by omega, by simp [show ¬(x1 ≤ w) by omega]⟩
    · exact ⟨hw.2, by simp [hw.1]⟩
  · intro j hj; simp at hj

private lemma mem_S0_false {x1 x2 : ℕ} (p : Fin x1) : p.1 ∈ S0 x1 x2 false := by
  simp [S0, p.2]

private lemma mem_S0_true {x1 x2 : ℕ} (l : Fin x2) : x1 + l.1 ∈ S0 x1 x2 true := by
  simp [S0]

private lemma good_append_or_side {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) (b : Bool) {u v : ℕ} (hu : u ∈ S b) (hv : v ∈ S b) :
    let w := x1 + x2 + gs.length
    let S' : Bool → Finset ℕ := fun b' => if b' = b then insert w (S b') else S b'
    Good x1 x2 S' (gs ++ [⟨GateOp.or, [u, v]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  have hu_lt : u < x1 + x2 + gs.length := hLt b u hu
  have hv_lt : v < x1 + x2 + gs.length := hLt b v hv
  dsimp only
  have hSub : ∀ b' : Bool, S b' ⊆ (if b' = b then insert (x1 + x2 + gs.length) (S b') else S b') := by
    intro b'
    by_cases hbb : b' = b
    · simp [hbb]
    · simp [hbb]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inr rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b' w hw
    simp only [List.length_append, List.length_singleton]
    by_cases hbb : b' = b
    · simp only [hbb, ite_true, Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · omega
      · have := hLt b w hw; omega
    · simp only [hbb, ite_false] at hw
      have := hLt b' w hw; omega
  · intro b' w hw
    by_cases hbb : b' = b
    · subst hbb
      simp only [ite_true, Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · right
        refine ⟨gs.length, by simp, rfl, ?_, ?_⟩
        · rw [gateAtL_append_self]
        · rw [gateAtL_append_self]
          intro t ht
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact hSub b' hu
          · exact hSub b' hv
      · rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
        · exact Or.inl h1
        · right
          refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
          · rw [gateAtL_append_lt _ _ _ hj]; exact hop
          · rw [gateAtL_append_lt _ _ _ hj]
            intro t ht
            exact hSub b' (hin t ht)
    · simp only [hbb, ite_false] at hw
      rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
      · exact Or.inl h1
      · right
        refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
        · rw [gateAtL_append_lt _ _ _ hj]; exact hop
        · rw [gateAtL_append_lt _ _ _ hj]
          intro t ht
          simp only [hbb, ite_false]
          exact hin t ht
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      rcases hAnd j hlt hop with ⟨a, c, hin, ha, hc⟩
      exact ⟨a, c, hin, hSub false ha, hSub true hc⟩
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hop
      cases hop

private lemma good_append_or_top {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) {u v : ℕ} (hu : u < x1 + x2 + gs.length) (hv : v < x1 + x2 + gs.length) :
    Good x1 x2 S (gs ++ [⟨GateOp.or, [u, v]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inr rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b w hw
    simp only [List.length_append, List.length_singleton]
    have := hLt b w hw; omega
  · intro b w hw
    rcases hSide b w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
    · exact Or.inl h1
    · right
      refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
      · rw [gateAtL_append_lt _ _ _ hj]; exact hop
      · rw [gateAtL_append_lt _ _ _ hj]; exact hin
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      exact hAnd j hlt hop
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hop
      cases hop

private lemma good_append_and {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) {a c : ℕ} (ha : a ∈ S false) (hc : c ∈ S true) :
    Good x1 x2 S (gs ++ [⟨GateOp.and, [a, c]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  have ha_lt : a < x1 + x2 + gs.length := hLt false a ha
  have hc_lt : c < x1 + x2 + gs.length := hLt true c hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inl rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b' w hw
    simp only [List.length_append, List.length_singleton]
    have := hLt b' w hw; omega
  · intro b' w hw
    rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
    · exact Or.inl h1
    · right
      refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
      · rw [gateAtL_append_lt _ _ _ hj]; exact hop
      · rw [gateAtL_append_lt _ _ _ hj]; exact hin
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      exact hAnd j hlt hop
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self]
      exact ⟨a, c, rfl, ha, hc⟩

private lemma addOrInSide {x1 x2 : ℕ} (b : Bool) (ws : List ℕ) (hne : ws ≠ []) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ u ∈ ws, u ∈ S b) →
      ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (w : ℕ),
        gs'.length = gs.length + (ws.length - 1) ∧
        Good x1 x2 S' gs' ∧
        (∀ b', S b' ⊆ S' b') ∧
        w ∈ S' b ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, wireVal (x1 + x2) gs' z w = ws.any (fun u => wireVal (x1 + x2) gs z u)) := by
  induction ws with
  | nil => exact absurd rfl hne
  | cons u rest ih =>
    intro S gs hG hws
    cases rest with
    | nil =>
      refine ⟨S, gs, u, by simp, hG, fun _ => Finset.Subset.rfl, hws u (by simp), ?_, ?_⟩
      · intro z i _; rfl
      · intro z; simp
    | cons v rest' =>
      have hne' : v :: rest' ≠ [] := List.cons_ne_nil v rest'
      have hws' : ∀ t ∈ v :: rest', t ∈ S b := fun t ht => hws t (List.mem_cons_of_mem u ht)
      rcases ih hne' S gs hG hws' with ⟨S1, gs1, w1, hlen1, hG1, hSub1, hw1, hPres1, hVal1⟩
      have hu1 : u ∈ S1 b := hSub1 b (hws u (by simp))
      let w := x1 + x2 + gs1.length
      let gs2 := gs1 ++ [⟨GateOp.or, [u, w1]⟩]
      let S2 : Bool → Finset ℕ := fun b' => if b' = b then insert w (S1 b') else S1 b'
      have hG2 : Good x1 x2 S2 gs2 := good_append_or_side hG1 b hu1 hw1
      have hSub2 : ∀ b', S b' ⊆ S2 b' := by
        intro b'
        refine Finset.Subset.trans (hSub1 b') ?_
        by_cases hbb : b' = b
        · simp [S2, hbb]
        · simp [S2, hbb]
      have hw2 : w ∈ S2 b := by simp [S2]
      have hu_lt : u < x1 + x2 + gs.length := hG.2.2.1 b u (hws u (by simp))
      refine ⟨S2, gs2, w, ?_, hG2, hSub2, hw2, ?_, ?_⟩
      · simp [gs2, hlen1]; omega
      · intro z i hi
        have hi1 : i < x1 + x2 + gs1.length := by omega
        rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
        exact hPres1 z i hi
      · intro z
        rw [wireVal_append_gate_self]
        simp only [List.map, GateOp.eval, List.any_cons]
        rw [hPres1 z u hu_lt, hVal1 z]
        simp

private lemma addOrTop {x1 x2 : ℕ} (ws : List ℕ) (hne : ws ≠ []) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ u ∈ ws, u < x1 + x2 + gs.length) →
      ∃ (gs' : List Gate) (w : ℕ),
        gs'.length = gs.length + (ws.length - 1) ∧
        Good x1 x2 S gs' ∧
        w < x1 + x2 + gs'.length ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, wireVal (x1 + x2) gs' z w = ws.any (fun u => wireVal (x1 + x2) gs z u)) := by
  induction ws with
  | nil => exact absurd rfl hne
  | cons u rest ih =>
    intro S gs hG hws
    cases rest with
    | nil =>
      refine ⟨gs, u, by simp, hG, hws u (by simp), ?_, ?_⟩
      · intro z i _; rfl
      · intro z; simp
    | cons v rest' =>
      have hne' : v :: rest' ≠ [] := List.cons_ne_nil v rest'
      have hws' : ∀ t ∈ v :: rest', t < x1 + x2 + gs.length :=
        fun t ht => hws t (List.mem_cons_of_mem u ht)
      rcases ih hne' S gs hG hws' with ⟨gs1, w1, hlen1, hG1, hw1, hPres1, hVal1⟩
      have hu_lt : u < x1 + x2 + gs.length := hws u (by simp)
      have hu1 : u < x1 + x2 + gs1.length := by omega
      let w := x1 + x2 + gs1.length
      let gs2 := gs1 ++ [⟨GateOp.or, [u, w1]⟩]
      have hG2 : Good x1 x2 S gs2 := good_append_or_top hG1 hu1 hw1
      refine ⟨gs2, w, ?_, hG2, ?_, ?_, ?_⟩
      · simp [gs2, hlen1]; omega
      · simp [gs2, w]
      · intro z i hi
        have hi1 : i < x1 + x2 + gs1.length := by omega
        rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
        exact hPres1 z i hi
      · intro z
        rw [wireVal_append_gate_self]
        simp only [List.map, GateOp.eval, List.any_cons]
        rw [hPres1 z u hu_lt, hVal1 z]
        simp

private abbrev Star (x1 x2 : ℕ) := (Fin x1 × List (Fin x2)) ⊕ (Fin x2 × List (Fin x1))

private def starSize {x1 x2 : ℕ} : Star x1 x2 → ℕ
  | Sum.inl (_, ls) => ls.length
  | Sum.inr (_, ps) => ps.length

private def starEval {x1 x2 : ℕ} (z : Fin (x1 + x2) → Bool) : Star x1 x2 → Bool
  | Sum.inl (p, ls) => z (Fin.castAdd x2 p) && ls.any (fun l => z (Fin.natAdd x1 l))
  | Sum.inr (l, ps) => ps.any (fun p => z (Fin.castAdd x2 p)) && z (Fin.natAdd x1 l)

private lemma wireVal_input_left {x1 x2 : ℕ} (gs : List Gate) (z : Fin (x1 + x2) → Bool)
    (p : Fin x1) :
    wireVal (x1 + x2) gs z p.1 = z (Fin.castAdd x2 p) := by
  induction gs using List.reverseRecOn with
  | nil =>
    unfold wireVal
    simp only [List.foldl_nil]
    have hlt : p.1 < x1 + x2 := by omega
    rw [getD_ofFn z p.1 hlt]
    rfl
  | append_singleton gs g ih =>
    rw [wireVal_append_gate_lt _ _ _ _ _ (by omega)]
    exact ih

private lemma wireVal_input_right {x1 x2 : ℕ} (gs : List Gate) (z : Fin (x1 + x2) → Bool)
    (l : Fin x2) :
    wireVal (x1 + x2) gs z (x1 + l.1) = z (Fin.natAdd x1 l) := by
  induction gs using List.reverseRecOn with
  | nil =>
    unfold wireVal
    simp only [List.foldl_nil]
    have hlt : x1 + l.1 < x1 + x2 := by omega
    rw [getD_ofFn z (x1 + l.1) hlt]
    rfl
  | append_singleton gs g ih =>
    rw [wireVal_append_gate_lt _ _ _ _ _ (by omega)]
    exact ih

private lemma addStar {x1 x2 : ℕ} (st : Star x1 x2) (hpos : 0 < starSize st)
    (S : Bool → Finset ℕ) (gs : List Gate)
    (hG : Good x1 x2 S gs) (hBase : ∀ b, S0 x1 x2 b ⊆ S b) :
    ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (w : ℕ),
      gs'.length = gs.length + starSize st ∧
      Good x1 x2 S' gs' ∧
      (∀ b, S b ⊆ S' b) ∧
      w < x1 + x2 + gs'.length ∧
      (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
      (∀ z, wireVal (x1 + x2) gs' z w = starEval z st) := by
  cases st with
  | inl pl =>
    rcases pl with ⟨p, ls⟩
    have hne_ls : ls ≠ [] := by
      intro h; simp [starSize, h] at hpos
    let ws : List ℕ := ls.map (fun l => x1 + l.1)
    have hne_ws : ws ≠ [] := by
      simp [ws, hne_ls]
    have hws_mem : ∀ u ∈ ws, u ∈ S true := by
      intro u hu
      simp only [ws, List.mem_map] at hu
      rcases hu with ⟨l, _, rfl⟩
      exact hBase true (mem_S0_true l)
    rcases addOrInSide true ws hne_ws S gs hG hws_mem with
      ⟨S1, gs1, wL, hlen1, hG1, hSub1, hwL, hPres1, hVal1⟩
    have hp1 : p.1 ∈ S1 false := hSub1 false (hBase false (mem_S0_false p))
    let w := x1 + x2 + gs1.length
    let gs2 := gs1 ++ [⟨GateOp.and, [p.1, wL]⟩]
    have hG2 : Good x1 x2 S1 gs2 := good_append_and hG1 hp1 hwL
    refine ⟨S1, gs2, w, ?_, hG2, hSub1, ?_, ?_, ?_⟩
    · simp only [gs2, List.length_append, List.length_singleton, hlen1, ws, List.length_map,
        starSize]
      have : 0 < ls.length := by simpa [starSize] using hpos
      omega
    · simp [gs2, w]
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
      exact hPres1 z i hi
    · intro z
      rw [wireVal_append_gate_self]
      simp only [List.map, GateOp.eval, starEval]
      rw [wireVal_input_left, hVal1 z]
      simp only [ws, List.any_map]
      have hfn : (fun l : Fin x2 => wireVal (x1 + x2) gs z (x1 + l.1)) =
          (fun l : Fin x2 => z (Fin.natAdd x1 l)) := by
        funext l
        exact wireVal_input_right gs z l
      simp [Function.comp_def, hfn]
  | inr lp =>
    rcases lp with ⟨l, ps⟩
    have hne_ps : ps ≠ [] := by
      intro h; simp [starSize, h] at hpos
    let ws : List ℕ := ps.map (fun p => p.1)
    have hne_ws : ws ≠ [] := by
      simp [ws, hne_ps]
    have hws_mem : ∀ u ∈ ws, u ∈ S false := by
      intro u hu
      simp only [ws, List.mem_map] at hu
      rcases hu with ⟨p, _, rfl⟩
      exact hBase false (mem_S0_false p)
    rcases addOrInSide false ws hne_ws S gs hG hws_mem with
      ⟨S1, gs1, wP, hlen1, hG1, hSub1, hwP, hPres1, hVal1⟩
    have hl1 : x1 + l.1 ∈ S1 true := hSub1 true (hBase true (mem_S0_true l))
    let w := x1 + x2 + gs1.length
    let gs2 := gs1 ++ [⟨GateOp.and, [wP, x1 + l.1]⟩]
    have hG2 : Good x1 x2 S1 gs2 := good_append_and hG1 hwP hl1
    refine ⟨S1, gs2, w, ?_, hG2, hSub1, ?_, ?_, ?_⟩
    · simp only [gs2, List.length_append, List.length_singleton, hlen1, ws, List.length_map,
        starSize]
      have : 0 < ps.length := by simpa [starSize] using hpos
      omega
    · simp [gs2, w]
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
      exact hPres1 z i hi
    · intro z
      rw [wireVal_append_gate_self]
      simp only [List.map, GateOp.eval, starEval]
      rw [wireVal_input_right, hVal1 z]
      simp only [ws, List.any_map]
      have hfn : (fun p : Fin x1 => wireVal (x1 + x2) gs z p.1) =
          (fun p : Fin x1 => z (Fin.castAdd x2 p)) := by
        funext p
        exact wireVal_input_left gs z p
      simp [Function.comp_def, hfn]

private lemma addStars {x1 x2 : ℕ} (stars : List (Star x1 x2))
    (hpos : ∀ st ∈ stars, 0 < starSize st) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ b, S0 x1 x2 b ⊆ S b) →
      ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (ws : List ℕ),
        gs'.length = gs.length + (stars.map starSize).sum ∧
        ws.length = stars.length ∧
        Good x1 x2 S' gs' ∧
        (∀ w ∈ ws, w < x1 + x2 + gs'.length) ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, ws.any (fun w => wireVal (x1 + x2) gs' z w) = stars.any (fun st => starEval z st)) := by
  induction stars with
  | nil =>
    intro S gs hG _
    refine ⟨S, gs, [], by simp, rfl, hG, by simp, ?_, ?_⟩
    · intro z i _; rfl
    · intro z; simp
  | cons st rest ih =>
    intro S gs hG hBase
    rcases addStar st (hpos st (by simp)) S gs hG hBase with
      ⟨S1, gs1, w1, hlen1, hG1, hSub1, hw1, hPres1, hVal1⟩
    have hBase1 : ∀ b, S0 x1 x2 b ⊆ S1 b := fun b => Finset.Subset.trans (hBase b) (hSub1 b)
    have hpos_rest : ∀ s ∈ rest, 0 < starSize s := fun s hs => hpos s (List.mem_cons_of_mem st hs)
    rcases ih hpos_rest S1 gs1 hG1 hBase1 with
      ⟨S2, gs2, ws2, hlen2, hwslen2, hG2, hws2_lt, hPres2, hVal2⟩
    refine ⟨S2, gs2, w1 :: ws2, ?_, ?_, hG2, ?_, ?_, ?_⟩
    · simp [hlen2, hlen1, Nat.add_assoc]
    · simp [hwslen2]
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · omega
      · exact hws2_lt w hw
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [hPres2 z i hi1]
      exact hPres1 z i hi
    · intro z
      simp only [List.any_cons]
      rw [hPres2 z w1 hw1, hVal1 z, hVal2 z]

private lemma circuit_from_good {x1 x2 : ℕ} (S : Bool → Finset ℕ) (gs : List Gate) (out : ℕ)
    (hG : Good x1 x2 S gs) :
    let C : Circuit := ⟨gs, out⟩
    IsAO2 (x1 + x2) C ∧
    (∀ b : Bool, ∀ w ∈ S b,
      (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
      ∃ j < C.size, w = x1 + x2 + j ∧ (gateAt C j).op = GateOp.or ∧
        ∀ u ∈ (gateAt C j).inputs, u ∈ S b) ∧
    (∀ j < C.size, (gateAt C j).op = GateOp.and →
      ∃ a c : ℕ, (gateAt C j).inputs = [a, c] ∧ a ∈ S false ∧ c ∈ S true) := by
  rcases hG with ⟨hAO, hRB, _, hSide, hAnd⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg; exact (hAO g hg).1
  · intro j hj i hi; exact hRB j hj i hi
  · intro g hg; exact (hAO g hg).2
  · intro b w hw; exact hSide b w hw
  · intro j hj hop; exact hAnd j hj hop

end A3692

open A3692 in
theorem t3692 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)),   (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) →     ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Bool → Finset ℕ),       PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧         x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧           (∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x3 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) ∧             have x9 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x7;             (∀ (x10 : Bool), ∀ x11 ∈ x8 x10, x11 < x1 + x2 ∧ Decidable.decide (x1 ≤ x11) = x10 ∨ ∃ x13 < x7.size, x11 = x1 + x2 + x13 ∧ (x9 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x14 ∈ (x9 x13).inputs, x14 ∈ x8 x10) ∧ ∀ x10 < x7.size, (x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (x9 x10).inputs = [x13, x14] ∧ x13 ∈ x8 Bool.false ∧ x14 ∈ x8 Bool.true := by
  intro x1 x2 E A B hcov
  by_cases hE : E = ∅
  · subst hE
    refine ⟨⟨[], x1 + x2⟩, fun _ => ∅, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro g hg; cases hg
      · intro j hj; simp at hj
      · intro g hg; cases hg
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    · intro z
      simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_nil, Finset.notMem_empty,
        false_and, exists_false, decide_false]
      exact getD_of_ge (List.ofFn z) (x1 + x2) (by simp)
    · intro b w hw; simp at hw
    · intro j hj; simp [PEqualNP.CircuitLowerBounds.Circuit.size] at hj
  · have hE_ne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hE
    let NA : Fin x1 → Finset (Fin x2) := fun p => Finset.univ.filter (fun l => (p, l) ∈ E)
    let NB : Fin x2 → Finset (Fin x1) := fun l => Finset.univ.filter (fun p => (p, l) ∈ E ∧ p ∉ A)
    let A' : Finset (Fin x1) := A.filter (fun p => (NA p).Nonempty)
    let B' : Finset (Fin x2) := B.filter (fun l => (NB l).Nonempty)
    let starsA : List (Star x1 x2) := A'.toList.map (fun p => Sum.inl (p, (NA p).toList))
    let starsB : List (Star x1 x2) := B'.toList.map (fun l => Sum.inr (l, (NB l).toList))
    let stars : List (Star x1 x2) := starsA ++ starsB
    have hpos : ∀ st ∈ stars, 0 < starSize st := by
      intro st hst
      simp only [stars, starsA, starsB, List.mem_append, List.mem_map, Finset.mem_toList] at hst
      rcases hst with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
      · simp only [starSize, Finset.length_toList]
        exact Finset.card_pos.mpr (Finset.mem_filter.mp hp).2
      · simp only [starSize, Finset.length_toList]
        exact Finset.card_pos.mpr (Finset.mem_filter.mp hl).2
    have hsumA : (starsA.map starSize).sum = ∑ p ∈ A', (NA p).card := by
      have h1 : (starsA.map starSize) = A'.toList.map (fun p => (NA p).card) := by
        simp [starsA, starSize, Function.comp_def]
      rw [h1, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    have hsumB : (starsB.map starSize).sum = ∑ l ∈ B', (NB l).card := by
      have h1 : (starsB.map starSize) = B'.toList.map (fun l => (NB l).card) := by
        simp [starsB, starSize, Function.comp_def]
      rw [h1, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    have hcardE : (∑ p ∈ A', (NA p).card) + (∑ l ∈ B', (NB l).card) = E.card := by
      let EA : Finset (Fin x1 × Fin x2) := A'.biUnion (fun p => (NA p).image (fun l => (p, l)))
      let EB : Finset (Fin x1 × Fin x2) := B'.biUnion (fun l => (NB l).image (fun p => (p, l)))
      have hEA_card : EA.card = ∑ p ∈ A', (NA p).card := by
        rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl ?_
          intro p _
          exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
        · intro p1 _ p2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro e he1 he2
          simp only [Finset.mem_image] at he1 he2
          rcases he1 with ⟨l1, _, rfl⟩
          rcases he2 with ⟨l2, _, heq⟩
          exact hne (Prod.mk.inj heq).1.symm
      have hEB_card : EB.card = ∑ l ∈ B', (NB l).card := by
        rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl ?_
          intro l _
          exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)
        · intro l1 _ l2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro e he1 he2
          simp only [Finset.mem_image] at he1 he2
          rcases he1 with ⟨p1, _, rfl⟩
          rcases he2 with ⟨p2, _, heq⟩
          exact hne (Prod.mk.inj heq).2.symm
      have hdisj : Disjoint EA EB := by
        rw [Finset.disjoint_left]
        intro e he1 he2
        simp only [EA, EB, Finset.mem_biUnion, Finset.mem_image] at he1 he2
        rcases he1 with ⟨p1, hp1, l1, _, rfl⟩
        rcases he2 with ⟨l2, _, p2, hp2, heq⟩
        have hp_eq : p2 = p1 := (Prod.mk.inj heq).1
        subst hp_eq
        have hp1A : p2 ∈ A := (Finset.mem_filter.mp hp1).1
        have hp2nA : p2 ∉ A := (Finset.mem_filter.mp hp2).2.2
        exact hp2nA hp1A
      have hunion : EA ∪ EB = E := by
        ext ⟨p, l⟩
        simp only [EA, EB, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
        constructor
        · rintro (⟨p1, _, l1, hl1, heq⟩ | ⟨l1, _, p1, hp1, heq⟩)
          · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            exact (Finset.mem_filter.mp hl1).2
          · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            exact (Finset.mem_filter.mp hp1).2.1
        · intro hpl
          by_cases hpA : p ∈ A
          · left
            refine ⟨p, Finset.mem_filter.mpr ⟨hpA, ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩⟩⟩,
              l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩, rfl⟩
          · right
            have hlB : l ∈ B := (hcov (p, l) hpl).resolve_left hpA
            refine ⟨l, Finset.mem_filter.mpr ⟨hlB, ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩⟩⟩,
              p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩, rfl⟩
      rw [← hEA_card, ← hEB_card, ← Finset.card_union_of_disjoint hdisj, hunion]
    have hsum_stars : (stars.map starSize).sum = E.card := by
      simp only [stars, List.map_append, List.sum_append, hsumA, hsumB, hcardE]
    have hstars_len : stars.length = A'.card + B'.card := by
      simp [stars, starsA, starsB]
    have hstars_ne : stars ≠ [] := by
      intro hnil
      have h0 : E.card = 0 := by
        rw [← hsum_stars, hnil]; rfl
      exact (Finset.card_pos.mpr hE_ne).ne' h0
    rcases addStars stars hpos (S0 x1 x2) [] (good_init x1 x2) (fun _ => Finset.Subset.rfl) with
      ⟨S1, gs1, ws1, hlen1, hwslen1, hG1, hws1_lt, _, hVal1⟩
    have hws1_ne : ws1 ≠ [] := by
      intro hnil
      apply hstars_ne
      apply List.eq_nil_of_length_eq_zero
      rw [← hwslen1, hnil]
      rfl
    rcases addOrTop ws1 hws1_ne S1 gs1 hG1 hws1_lt with
      ⟨gs2, wOut, hlen2, hG2, _, hPres2, hVal2⟩
    let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs2, wOut⟩
    have hC := circuit_from_good S1 gs2 wOut hG2
    refine ⟨C, S1, hC.1, ?_, ?_, hC.2.1, hC.2.2⟩
    · have hA' : A'.card ≤ A.card := Finset.card_filter_le _ _
      have hB' : B'.card ≤ B.card := Finset.card_filter_le _ _
      have hk_pos : 1 ≤ ws1.length := by
        cases ws1 with
        | nil => exact absurd rfl hws1_ne
        | cons _ _ => simp
      simp only [C, PEqualNP.CircuitLowerBounds.Circuit.size, hlen2, hlen1, List.length_nil,
        Nat.zero_add, hsum_stars, hwslen1, hstars_len]
      omega
    · intro z
      have hcf : PEqualNP.MetaComplexity.circuitFun (x1 + x2) C z = wireVal (x1 + x2) gs2 z wOut := rfl
      rw [hcf, hVal2 z, hVal1 z]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨st, hst, hst_eval⟩
        simp only [stars, starsA, starsB, List.mem_append, List.mem_map, Finset.mem_toList] at hst
        rcases hst with ⟨p, _, rfl⟩ | ⟨l, _, rfl⟩
        · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList] at hst_eval
          rcases hst_eval with ⟨hzp, l, hl, hzl⟩
          exact ⟨p, l, (Finset.mem_filter.mp hl).2, hzp, hzl⟩
        · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList] at hst_eval
          rcases hst_eval with ⟨⟨p, hp, hzp⟩, hzl⟩
          exact ⟨p, l, (Finset.mem_filter.mp hp).2.1, hzp, hzl⟩
      · rintro ⟨p, l, hpl, hzp, hzl⟩
        by_cases hpA : p ∈ A
        · refine ⟨Sum.inl (p, (NA p).toList), ?_, ?_⟩
          · simp only [stars, starsA, List.mem_append, List.mem_map, Finset.mem_toList]
            left
            exact ⟨p, Finset.mem_filter.mpr ⟨hpA, ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩⟩⟩, rfl⟩
          · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList]
            exact ⟨hzp, l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩, hzl⟩
        · have hlB : l ∈ B := (hcov (p, l) hpl).resolve_left hpA
          refine ⟨Sum.inr (l, (NB l).toList), ?_, ?_⟩
          · simp only [stars, starsB, List.mem_append, List.mem_map, Finset.mem_toList]
            right
            exact ⟨l, Finset.mem_filter.mpr ⟨hlB, ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩⟩⟩, rfl⟩
          · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList]
            exact ⟨⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩, hzp⟩, hzl⟩

namespace B6579

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadK PEqualNP.TopForm

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


lemma mem_foldl_insertNew_of_acc (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ acc) : v ∈ L.foldl insertNew acc := by
  induction L generalizing acc with
  | nil => exact h
  | cons x L ih =>
    rw [List.foldl_cons]
    apply ih
    unfold insertNew
    split_ifs
    · exact h
    · exact List.mem_append_left _ h

lemma mem_foldl_insertNew_of_mem (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ L) : v ∈ L.foldl insertNew acc := by
  induction L generalizing acc with
  | nil => simp at h
  | cons x L ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.1 h with h1 | h1
    · apply mem_foldl_insertNew_of_acc
      subst h1
      unfold insertNew
      split_ifs with h2
      · exact h2
      · simp
    · exact ih _ h1

lemma mem_andStep_of (k : ℕ) (A B : List (List ℕ)) (u u2 : List ℕ) (hu : u ∈ A) (hu2 : u2 ∈ B) :
    capAdd k u u2 ∈ andStep k A B := by
  unfold andStep
  apply mem_foldl_insertNew_of_mem
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨u, hu, u2, hu2, rfl⟩

lemma mem_orFold (As : List (List (List ℕ))) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ acc ∨ ∃ A ∈ As, v ∈ A) :
    v ∈ As.foldl (fun acc A => A.foldl insertNew acc) acc := by
  induction As generalizing acc with
  | nil =>
    rcases h with h | ⟨A, hA, _⟩
    · exact h
    · simp at hA
  | cons A0 As ih =>
    rw [List.foldl_cons]
    apply ih
    rcases h with h | ⟨A, hA, hv⟩
    · exact Or.inl (mem_foldl_insertNew_of_acc _ _ _ h)
    · rcases List.mem_cons.1 hA with h1 | h1
      · subst h1
        exact Or.inl (mem_foldl_insertNew_of_mem _ _ _ hv)
      · exact Or.inr ⟨A, h1, hv⟩

lemma capAdd_map (L : List ℕ) (f g : ℕ → ℕ) (k : ℕ) :
    capAdd k (L.map f) (L.map g) = L.map (fun j => min (f j + g j) (k + 1)) := by
  unfold capAdd
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons, List.zipWith_cons_cons, ih]

def uv (L : List ℕ) (i : ℕ) : List ℕ := L.map fun j => if j = i then min 1 (1 + 1) else 0

lemma mem_setList {n : ℕ} (S : Finset (Fin n)) (w : ℕ) (hw : w < n) (h : (⟨w, hw⟩ : Fin n) ∈ S) :
    w ∈ setList S := by
  unfold setList
  simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  exact ⟨⟨w, hw⟩, h, rfl⟩

theorem inv (x1 x2 : ℕ) (C : Circuit) (x4 : Bool → Finset ℕ) (hC : IsAO2 (x1 + x2) C)
    (hx4 : ∀ (b : Bool), ∀ w ∈ x4 b, (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
      ∃ j < C.size, w = x1 + x2 + j ∧ (gateAt C j).op = GateOp.or ∧
        ∀ i ∈ (gateAt C j).inputs, i ∈ x4 b)
    (hand : ∀ j < C.size, (gateAt C j).op = GateOp.and →
      ∃ (a : ℕ) (c : ℕ), (gateAt C j).inputs = [a, c] ∧ a ∈ x4 false ∧ c ∈ x4 true)
    (S : Finset (Fin (x1 + x2))) :
    ∀ w, s2230_W (x1 + x2) C (setInput S) w = true →
      (∃ v ∈ s2230_RV C (x1 + x2) (setList S) 1 w, ∀ a ∈ v, a ≤ 1) ∧
      (∀ b, w ∈ x4 b → ∃ i, decide (x1 ≤ i) = b ∧
        uv (setList S) i ∈ s2230_RV C (x1 + x2) (setList S) 1 w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw
  obtain ⟨hAO, hRB, _⟩ := hC
  by_cases hwn : w < x1 + x2
  · have hS : (⟨w, hwn⟩ : Fin (x1 + x2)) ∈ S := by
      rw [s2230_W_input (x1 + x2) C _ w hwn] at hw
      simpa [setInput] using hw
    have hmem : w ∈ setList S := mem_setList S w hwn hS
    have hRV : s2230_RV C (x1 + x2) (setList S) 1 w = [uv (setList S) w] := by
      rw [s2230_RV_input C (x1 + x2) (setList S) 1 w hwn]
      unfold leafVectors uv
      rw [if_pos hmem]
    refine ⟨⟨uv (setList S) w, by rw [hRV]; exact List.mem_singleton_self _, ?_⟩, ?_⟩
    · intro a ha
      unfold uv at ha
      simp only [List.mem_map] at ha
      obtain ⟨j, _, rfl⟩ := ha
      split_ifs <;> omega
    · intro b hb
      refine ⟨w, ?_, by rw [hRV]; exact List.mem_singleton_self _⟩
      rcases hx4 b w hb with ⟨_, hside⟩ | ⟨j, _, hj, _⟩
      · exact hside
      · omega
  · by_cases hwl : w < x1 + x2 + C.gates.length
    swap
    · exfalso
      have hf : s2230_W (x1 + x2) C (setInput S) w = false := by
        unfold s2230_W
        exact s2230_getD_ge_length _ _ (by rw [s2230_wires_length]; omega)
      rw [hf] at hw
      exact Bool.false_ne_true hw
    obtain ⟨j, rfl⟩ : ∃ j, w = x1 + x2 + j := ⟨w - (x1 + x2), by omega⟩
    have hj : j < C.gates.length := by omega
    have hgW := s2230_W_gate (x1 + x2) C (setInput S) j hj
    obtain ⟨Rp, hRp, hRVj⟩ := s2230_RV_gate C (x1 + x2) (setList S) 1 j hj
    have hRB' : ∀ i ∈ (gateAt C j).inputs, i < x1 + x2 + j := hRB j hj
    have hmapW : ((gateAt C j).inputs.map fun i =>
        if i < x1 + x2 + j then s2230_W (x1 + x2) C (setInput S) i else false) =
        (gateAt C j).inputs.map fun i => s2230_W (x1 + x2) C (setInput S) i := by
      refine List.map_congr_left fun i hi => ?_
      rw [if_pos (hRB' i hi)]
    have hmapR : ((gateAt C j).inputs.map fun i => Rp.getD i []) =
        (gateAt C j).inputs.map fun i => s2230_RV C (x1 + x2) (setList S) 1 i := by
      refine List.map_congr_left fun i hi => ?_
      exact hRp i (hRB' i hi)
    have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or :=
      hAO (gateAt C j) (by rw [s2230_gateAt_eq C j hj]; exact List.getElem_mem hj)
    have hor_true : (gateAt C j).op = GateOp.or →
        ∃ i ∈ (gateAt C j).inputs, s2230_W (x1 + x2) C (setInput S) i = true := by
      intro ho
      have hw' := hw
      rw [hgW, hmapW, ho] at hw'
      simpa [GateOp.eval] using hw'
    have hor_mem : (gateAt C j).op = GateOp.or → ∀ i ∈ (gateAt C j).inputs,
        ∀ v ∈ s2230_RV C (x1 + x2) (setList S) 1 i,
          v ∈ s2230_RV C (x1 + x2) (setList S) 1 (x1 + x2 + j) := by
      intro ho i hi v hv
      rw [hRVj, s2230_FR_or _ _ _ _ ho, hmapR]
      apply mem_orFold
      exact Or.inr ⟨_, List.mem_map.2 ⟨i, hi, rfl⟩, hv⟩
    refine ⟨?_, ?_⟩
    · rcases hop with ho | ho
      · obtain ⟨a, c, hac, ha, hc⟩ := hand j hj ho
        have hw' := hw
        rw [hgW, hmapW, ho, hac] at hw'
        have hwa : s2230_W (x1 + x2) C (setInput S) a = true ∧
            s2230_W (x1 + x2) C (setInput S) c = true := by
          simpa [GateOp.eval] using hw'
        have hRBa : a < x1 + x2 + j := hRB' a (by rw [hac]; simp)
        have hRBc : c < x1 + x2 + j := hRB' c (by rw [hac]; simp)
        obtain ⟨ia, hia, hA⟩ := (ih a hRBa hwa.1).2 false ha
        obtain ⟨ic, hic, hCc⟩ := (ih c hRBc hwa.2).2 true hc
        have hne : ia ≠ ic := by
          rintro rfl
          rw [hia] at hic
          exact Bool.false_ne_true hic
        refine ⟨capAdd 1 (capAdd 1 ((setList S).map fun _ => 0) (uv (setList S) ia))
          (uv (setList S) ic), ?_, ?_⟩
        · rw [hRVj, s2230_FR_and _ _ _ _ ho, hmapR, hac]
          simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
          exact mem_andStep_of _ _ _ _ _
            (mem_andStep_of _ _ _ _ _ (List.mem_singleton_self _) hA) hCc
        · intro e he
          unfold uv at he
          rw [capAdd_map, capAdd_map] at he
          simp only [List.mem_map] at he
          obtain ⟨t, _, rfl⟩ := he
          split_ifs <;> omega
      · obtain ⟨i, hi, hwi⟩ := hor_true ho
        obtain ⟨v, hv, hle⟩ := (ih i (hRB' i hi) hwi).1
        exact ⟨v, hor_mem ho i hi v hv, hle⟩
    · intro b hb
      rcases hx4 b _ hb with ⟨hlt, _⟩ | ⟨j', _, hjj, ho, hins⟩
      · omega
      · have hjj' : j' = j := by omega
        subst hjj'
        obtain ⟨i, hi, hwi⟩ := hor_true ho
        obtain ⟨ia, hia, hA⟩ := (ih i (hRB' i hi) hwi).2 b (hins i hi)
        exact ⟨ia, hia, hor_mem ho i hi _ hA⟩

end B6579

theorem t6579 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Bool → Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x3 → (∀ (x6 : Bool), ∀ x7 ∈ x4 x6, x7 < x1 + x2 ∧ Decidable.decide (x1 ≤ x7) = x6 ∨ ∃ x9 < x3.size, x7 = x1 + x2 + x9 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).inputs, x10 ∈ x4 x6) → (∀ x7 < x3.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : ℕ) (x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).inputs = [x10, x11] ∧ x10 ∈ x4 Bool.false ∧ x11 ∈ x4 Bool.true) → PEqualNP.ReadK.IsReadK (x1 + x2) x3 (1 : ℕ) := by
  intro x1 x2 C x4 hC hx4 hand S hS
  have hout : PEqualNP.Outside.L_meta_2583.StarConstruction.B6579.s2230_W (x1 + x2) C (PEqualNP.ReadK.setInput S)
      C.output = true := hS.1
  obtain ⟨⟨v, hv, hle⟩, _⟩ :=
    PEqualNP.Outside.L_meta_2583.StarConstruction.B6579.inv x1 x2 C x4 hC hx4 hand S C.output hout
  unfold PEqualNP.ReadK.readsAtMost
  apply List.any_eq_true.2
  refine ⟨v, hv, ?_⟩
  apply List.all_eq_true.2
  intro a ha
  exact decide_eq_true (hle a ha)

end PEqualNP.Outside.L_meta_2583.StarConstruction

namespace PEqualNP.Outside.L_meta_2583.StarConstruction

theorem exists_read_one : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)), (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧ (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) ∧ PEqualNP.ReadK.IsReadK (x1 + x2) x7 (1 : ℕ) := by
  intro x1 x2 x3 x4 x5 hcov
  obtain ⟨C, F, hao, hsize, hfun, hF1, hF2⟩ := PEqualNP.Outside.L_meta_2583.StarConstruction.t3692 x1 x2 x3 x4 x5 hcov
  exact ⟨C, hao, hsize, hfun, PEqualNP.Outside.L_meta_2583.StarConstruction.t6579 x1 x2 C F hao hF1 hF2⟩


end PEqualNP.Outside.L_meta_2583.StarConstruction

namespace PEqualNP.Outside.L_meta_2583.StarConstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def incidenceEdges (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] :
    Finset (Fin N × Fin N) := Finset.univ.filter fun e => I e.1 e.2

lemma incidenceEdges_card (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hline : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1) :
    (incidenceEdges N I).card = N * (q + 1) := by
  unfold incidenceEdges
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [← Finset.card_filter, hline]
  simp

theorem incidence_read_one_upper (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hline : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true)) ∧
      D.size ≤ N * (q + 2) - 1 ∧ PEqualNP.ReadK.IsReadK (N + N) D 1 := by
  obtain ⟨D, hAO, hsize, hfun, hread⟩ := exists_read_one N N (incidenceEdges N I)
    ∅ Finset.univ (by intro e he; exact Or.inr (Finset.mem_univ e.2))
  refine ⟨D, hAO, ?_, ?_, hread⟩
  · simpa only [incidenceEdges, Finset.mem_filter, Finset.mem_univ, true_and] using hfun
  · simpa only [incidenceEdges_card q N I hline, Finset.card_empty,
      Finset.card_univ, Fintype.card_fin, Nat.add_zero,
      show N * (q + 1) + N = N * (q + 2) by ring] using hsize

theorem normalize_of_size_bound (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit)
    (hline : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hsize : N * (q + 2) - 1 ≤ C.size) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ y : Fin (N + N) → Bool, circuitFun (N + N) D y =
        decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧
          y (Fin.natAdd N l) = true)) ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1 := by
  obtain ⟨D, hAO, hfun, hbound, hread⟩ := incidence_read_one_upper q N I hline
  exact ⟨D, hAO, hfun, hbound.trans hsize, hread⟩

end PEqualNP.Outside.L_meta_2583.StarConstruction


namespace PEqualNP.Outside.L_meta_2583
open PEqualNP.CircuitLowerBounds

lemma read_one_plane_floor (q N : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (ao : PEqualNP.TopForm.IsAO2 (N + N) C)
    (computes : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true))
    (readOne : PEqualNP.ReadK.IsReadK (N + N) C 1) :
    N * (q + 2) ≤ C.size + 1 := by
  classical
  have compE : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z =
        decide (∃ p l : Fin N, (p, l) ∈ PlaneGeometry.edges I ∧
          z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
    intro z
    simpa only [PlaneGeometry.edges, Finset.mem_filter, Finset.mem_univ, true_and] using computes z
  obtain ⟨A, B, covers, bound⟩ := ReadOneCost.cover_bound N N (PlaneGeometry.edges I) C
    (PlaneGeometry.no_rectangle I hu) ao compE readOne
  have coverMin := PlaneGeometry.cover_edges I (by omega) hN hl hu A B covers
  rw [PlaneGeometry.edges_card I hl] at bound
  have arithmetic : N * (q + 2) = N * (q + 1) + N := by ring
  rw [arithmetic]
  omega

end PEqualNP.Outside.L_meta_2583


namespace PEqualNP.Outside.L_meta_2583
open PEqualNP.CircuitLowerBounds

lemma normalization_iff_exact_cost (q N : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    (∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y =
        decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧
          y (Fin.natAdd N l) = true)) ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1) ↔
    N * (q + 2) ≤ C.size + 1 := by
  constructor
  · rintro ⟨D, ao, computes, size, readOne⟩
    exact (read_one_plane_floor q N I D hq hN hl hu ao computes readOne).trans
      (Nat.add_le_add_right size 1)
  · intro lower
    apply StarConstruction.normalize_of_size_bound q N I C hl
    omega

end PEqualNP.Outside.L_meta_2583


namespace PEqualNP.Outside.L_meta_2583


-- One lift step keeps the two-input AND/OR form, the output inside the wires, the size
-- and the function. The gate list is split at the lifted gate; the wires of the erased
-- circuit are the old wires under the renaming whenever the lifted operand is false, and
-- when it is true both outputs are true.
namespace LiftCorrect

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.MetaComplexity.NestedCover

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem length_wiresFrom (gs : List Gate) : ∀ w : List Bool,
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem wiresFrom_input (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have s : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s, ih _ i (by simp; omega), getD_snoc_ne _ _ _ _ (by omega)]

theorem wiresFrom_or (U : List Bool) (a b : ℕ) :
    wiresFrom [(⟨GateOp.or, [a, b]⟩ : Gate)] U = U ++ [(U.getD a false || U.getD b false)] := by
  simp [wiresFrom, GateOp.eval]

theorem lift_last (n : ℕ) (A : List Gate) (a b : ℕ) (w : List Bool) (hw : w.length = n) :
    (wiresFrom (A ++ [⟨GateOp.or, [a, b]⟩]) w).getD (n + A.length) false
      = ((wiresFrom A w).getD a false || (wiresFrom A w).getD b false) := by
  rw [wiresFrom_append, wiresFrom_or, ← hw, ← length_wiresFrom A w, getD_snoc_eq]

theorem eval_eq (C : Circuit) (w : List Bool) :
    C.eval w = (wiresFrom C.gates w).getD C.output false := rfl

-- Every gate of the list reads only wires below its own index, the first gate being
-- wire k.
def RBfrom : ℕ → List Gate → Prop
  | _, [] => True
  | k, g :: gs => (∀ i ∈ g.inputs, i < k) ∧ RBfrom (k + 1) gs

theorem rbfrom_append : ∀ (l1 l2 : List Gate) (k : ℕ),
    RBfrom k (l1 ++ l2) ↔ RBfrom k l1 ∧ RBfrom (k + l1.length) l2
  | [], l2, k => by simp [RBfrom]
  | g :: l1, l2, k => by
    have ih := rbfrom_append l1 l2 (k + 1)
    have e : k + 1 + l1.length = k + (l1.length + 1) := by omega
    simp only [List.cons_append, RBfrom, List.length_cons, ih, e]
    tauto

theorem rbfrom_iff (d : Gate) : ∀ (gs : List Gate) (k : ℕ),
    RBfrom k gs ↔ ∀ j < gs.length, ∀ i ∈ (gs.getD j d).inputs, i < k + j
  | [], k => by simp [RBfrom]
  | g :: gs, k => by
    have ih := rbfrom_iff d gs (k + 1)
    simp only [RBfrom, ih]
    constructor
    · rintro ⟨h0, h1⟩ j hj i hi
      cases j with
      | zero => exact h0 i (by simpa using hi)
      | succ j =>
        have := h1 j (by simpa using hj) i (by simpa using hi)
        omega
    · intro h
      refine ⟨fun i hi => by simpa using h 0 (by simp) i (by simpa using hi), fun j hj i hi => ?_⟩
      have := h (j + 1) (by simpa using hj) i (by simpa using hi)
      omega

theorem rbfrom_erase (n m p : ℕ) (hp : p < n + m) : ∀ (post : List Gate) (k : ℕ),
    n + m ≤ k → RBfrom (k + 1) post →
      RBfrom k (post.map fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩)
  | [], _, _, _ => trivial
  | g :: post, k, hk, h => by
    refine ⟨?_, rbfrom_erase n m p hp post (k + 1) (by omega) h.2⟩
    intro i hi
    obtain ⟨i0, hi0, rfl⟩ := List.mem_map.1 hi
    have := h.1 i0 hi0
    unfold eraseRedirect
    split_ifs <;> omega

-- The wires of the erased list are the old wires under the renaming.
theorem sim (n m p : ℕ) (hp : p < n + m) (post : List Gate) :
    ∀ U V : List Bool, V.length = U.length + 1 → n + m ≤ U.length →
      (∀ i, U.getD (eraseRedirect n m p i) false = V.getD i false) →
      ∀ i, (wiresFrom (post.map fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) U).getD
          (eraseRedirect n m p i) false = (wiresFrom post V).getD i false := by
  induction post with
  | nil => intro U V _ _ h; exact h
  | cons g post ih =>
    intro U V hl hU h
    have s1 : wiresFrom ((g :: post).map fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) U
        = wiresFrom (post.map fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩)
          (U ++ [g.op.eval ((g.inputs.map (eraseRedirect n m p)).map fun i => U.getD i false)]) :=
      rfl
    have s2 : wiresFrom (g :: post) V
        = wiresFrom post (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) := rfl
    have hval : g.op.eval ((g.inputs.map (eraseRedirect n m p)).map fun i => U.getD i false)
        = g.op.eval (g.inputs.map fun i => V.getD i false) := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact h a
    rw [s1, s2, hval]
    apply ih _ _ (by simp [hl]) (by simp; omega)
    intro i
    by_cases hi : i = V.length
    · have hr : eraseRedirect n m p i = U.length := by
        unfold eraseRedirect
        split_ifs <;> omega
      rw [hr, hi, getD_snoc_eq, getD_snoc_eq]
    · have hr : eraseRedirect n m p i ≠ U.length := by
        unfold eraseRedirect
        split_ifs <;> omega
      rw [getD_snoc_ne _ _ _ _ hi, getD_snoc_ne _ _ _ _ hr]
      exact h i

theorem sim_base (n m p : ℕ) (W1 : List Bool) (hW1 : W1.length = n + m) (vg : Bool)
    (hvg : vg = W1.getD p false) :
    ∀ i, W1.getD (eraseRedirect n m p i) false = (W1 ++ [vg]).getD i false := by
  intro i
  by_cases hi : i = n + m
  · have hr : eraseRedirect n m p i = p := by
      unfold eraseRedirect
      split_ifs
      rfl
    rw [hr, hi, ← hW1, getD_snoc_eq, hvg]
  · rw [getD_snoc_ne _ _ _ _ (by omega)]
    unfold eraseRedirect
    split_ifs with h2
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    · rfl

theorem lift_eval (n m p h out : ℕ) (hp : p < n + m) (hh : h < n + m) (post : List Gate)
    (W1 : List Bool) (hW1 : W1.length = n + m) (vg : Bool)
    (hvg : vg = (W1.getD p false || W1.getD h false))
    (hbelow : (wiresFrom post (W1 ++ [vg])).getD h false = true →
      (wiresFrom post (W1 ++ [vg])).getD out false = true) :
    ((wiresFrom (post.map fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) W1).getD
        (eraseRedirect n m p out) false ||
      (wiresFrom (post.map fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) W1).getD h false)
      = (wiresFrom post (W1 ++ [vg])).getD out false := by
  have hUh : (wiresFrom (post.map fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) W1).getD
      h false = W1.getD h false := wiresFrom_input _ _ _ (by omega)
  have hVh : (wiresFrom post (W1 ++ [vg])).getD h false = W1.getD h false := by
    rw [wiresFrom_input _ _ _ (by simp; omega), getD_snoc_ne _ _ _ _ (by omega)]
  rw [hUh]
  rw [hVh] at hbelow
  cases hhv : W1.getD h false with
  | true =>
    rw [Bool.or_true]
    exact (hbelow hhv).symm
  | false =>
    rw [Bool.or_false]
    have hvg' : vg = W1.getD p false := by rw [hvg, hhv, Bool.or_false]
    exact sim n m p hp post W1 (W1 ++ [vg]) (by simp) (by omega)
      (sim_base n m p W1 hW1 vg hvg') out

theorem lift_shape (n : ℕ) (C : Circuit) (pre post : List Gate) (gm : Gate) (p h : ℕ)
    (hs : C.gates = pre ++ gm :: post) :
    liftAt n C pre.length p h =
      ⟨(pre ++ post.map fun g => ⟨g.op, g.inputs.map (eraseRedirect n pre.length p)⟩) ++
          [⟨GateOp.or, [eraseRedirect n pre.length p C.output, h]⟩],
        n + (pre ++ post.map fun g =>
          (⟨g.op, g.inputs.map (eraseRedirect n pre.length p)⟩ : Gate)).length⟩ := by
  have hlt : pre.length < C.gates.length := by rw [hs]; simp
  have htake : C.gates.take pre.length = pre := by rw [hs]; exact List.take_left' rfl
  have hdrop : C.gates.drop (pre.length + 1) = post := by
    rw [hs]
    have e : pre ++ gm :: post = (pre ++ [gm]) ++ post := by simp
    rw [e]
    exact List.drop_left' (by simp)
  have hE : eraseGate n C pre.length p =
      ⟨pre ++ post.map fun g => ⟨g.op, g.inputs.map (eraseRedirect n pre.length p)⟩,
        eraseRedirect n pre.length p C.output⟩ := by
    unfold eraseGate
    rw [ite_eq_left hlt, htake, hdrop]
  unfold liftAt
  rw [hE]

end LiftCorrect

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.Outside.L_meta_2583.LiftCorrect

lemma liftCorrect : ∀ (x1 : ℕ) (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output < x1 + x2.gates.length → PEqualNP.CircuitMoves.Lift x1 x2 x3 → PEqualNP.TopForm.IsAO2 x1 x3 ∧ x3.output < x1 + x3.gates.length ∧ x3.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x3 = PEqualNP.MetaComplexity.circuitFun x1 x2 := by
  intro n C C' hC hout hL
  obtain ⟨m, hm, p, hp, h, hh, hnh, hgate, hbelow, rfl⟩ := hL
  obtain ⟨hAO, hRB, hTwo⟩ := hC
  obtain ⟨gm, hgm, hgmval⟩ : ∃ gm : Gate, C.gates[m]? = some gm ∧
      (gm = ⟨GateOp.or, [p, h]⟩ ∨ gm = ⟨GateOp.or, [h, p]⟩) := by
    rcases hgate with e | e
    · exact ⟨_, e, Or.inl rfl⟩
    · exact ⟨_, e, Or.inr rfl⟩
  obtain ⟨pre, post, hs, rfl⟩ : ∃ pre post : List Gate,
      C.gates = pre ++ gm :: post ∧ pre.length = m := by
    obtain ⟨hlt, hval⟩ := List.getElem?_eq_some_iff.1 hgm
    refine ⟨C.gates.take m, C.gates.drop (m + 1), ?_, by simp [List.length_take]; omega⟩
    rw [← hval, ← List.drop_eq_getElem_cons hlt, List.take_append_drop]
  rw [lift_shape n C pre post gm p h hs]
  have hRB' : RBfrom n (pre ++ gm :: post) := by
    rw [← hs]
    exact (rbfrom_iff ⟨GateOp.or, []⟩ C.gates n).2 hRB
  rw [rbfrom_append] at hRB'
  obtain ⟨hRBpre, hRBrest⟩ := hRB'
  have hRBpost : RBfrom (n + pre.length + 1) post := hRBrest.2
  have hlen : C.gates.length = pre.length + post.length + 1 := by
    rw [hs]
    simp
    omega
  have hmemC : ∀ g : Gate, g ∈ pre ∨ g ∈ post → g ∈ C.gates := by
    intro g hg
    rw [hs]
    rcases hg with hg | hg
    · exact List.mem_append_left _ hg
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hg)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
    rcases hg with (hg | ⟨g0, hg0, rfl⟩) | rfl
    · exact hAO g (hmemC g (Or.inl hg))
    · exact hAO g0 (hmemC g0 (Or.inr hg0))
    · exact Or.inr rfl
  · refine (rbfrom_iff ⟨GateOp.or, []⟩ _ n).1 ?_
    rw [rbfrom_append, rbfrom_append]
    refine ⟨⟨hRBpre, rbfrom_erase n pre.length p hp post _ (le_refl _) hRBpost⟩, ?_, trivial⟩
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_append, List.length_map]
    rcases hi with rfl | rfl
    · unfold eraseRedirect
      split_ifs <;> omega
    · omega
  · intro g hg
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
    rcases hg with (hg | ⟨g0, hg0, rfl⟩) | rfl
    · exact hTwo g (hmemC g (Or.inl hg))
    · simpa using hTwo g0 (hmemC g0 (Or.inr hg0))
    · rfl
  · simp
  · simp [Circuit.size, hlen]
    omega
  · funext x
    have hW1 : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
      rw [length_wiresFrom]
      simp
    have hW : wiresFrom C.gates (List.ofFn x) = wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [gm.op.eval (gm.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
      rw [hs, wiresFrom_append]
      rfl
    have hvg : gm.op.eval (gm.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)
        = ((wiresFrom pre (List.ofFn x)).getD p false
          || (wiresFrom pre (List.ofFn x)).getD h false) := by
      rcases hgmval with rfl | rfl
      · simp [GateOp.eval]
      · simp [GateOp.eval, Bool.or_comm]
    have key := lift_eval n pre.length p h C.output hp hh post (wiresFrom pre (List.ofFn x)) hW1
      _ hvg (by
        have hb := hbelow x
        rw [← hW]
        exact hb)
    unfold PEqualNP.MetaComplexity.circuitFun
    rw [eval_eq C, hW, ← key, eval_eq, lift_last n _ _ _ _ (by simp), wiresFrom_append]


namespace LiftNormalize

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def evalGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma evalGates_length (gs : List Gate) (w : List Bool) :
    (evalGates gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalGates]
  | cons g gs ih =>
    simp only [evalGates, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

lemma evalGates_append (gs1 gs2 : List Gate) (w : List Bool) :
    evalGates (gs1 ++ gs2) w = evalGates gs2 (evalGates gs1 w) := by
  simp [evalGates, List.foldl_append]

lemma evalGates_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (evalGates gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [evalGates, List.foldl_cons] at ih ⊢
    have hk' : k < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
      simp
      omega
    rw [ih _ hk']
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma evalGates_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (evalGates gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (evalGates (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp
  conv_lhs => rw [hsplit]
  rw [evalGates_append, evalGates_append]
  set w1 := evalGates (gs.take j) w
  have hw1 : w1.length = w.length + j := by
    rw [evalGates_length, List.length_take]
    omega
  have hlt : w.length + j < (evalGates [gs[j]] w1).length := by
    rw [evalGates_length, hw1]
    simp
  rw [evalGates_getD_lt _ _ _ hlt]
  simp only [evalGates, List.foldl_cons, List.foldl_nil]
  rw [← hw1]
  simp [List.getD_eq_getElem?_getD]

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma wires_getD_gate (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (x : List Bool) (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (n + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (C.wires x).getD i false) := by
  change (evalGates C.gates x).getD (n + j) false = _
  have h1 := evalGates_getD_gate C.gates x j hj
  rw [hx] at h1
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi_lt : i < n + j := by
    have := hRB j hj i
    rw [gateAt_eq_getElem C j hj] at this
    exact this hi
  have hlen : (evalGates (C.gates.take j) x).length = n + j := by
    rw [evalGates_length, hx, List.length_take]
    omega
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  symm
  change (evalGates C.gates x).getD i false = (evalGates (C.gates.take j) x).getD i false
  conv_lhs => rw [hsplit, evalGates_append]
  exact evalGates_getD_lt (C.gates.drop j) (evalGates (C.gates.take j) x) i (by omega)

lemma eraseRedirect_lt (n m p j u : ℕ) (hp : p < n + m) (hmj : m ≤ j) (hu : u < n + (j + 1)) :
    eraseRedirect n m p u < n + j := by
  unfold eraseRedirect
  split_ifs <;> omega

lemma eraseGate_gates_length (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates.length = C.gates.length - 1 := by
  simp [eraseGate, hm]
  omega

lemma liftAt_gates_length (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length) :
    (liftAt n C m p h).gates.length = C.gates.length := by
  simp [liftAt, eraseGate_gates_length n C m p hm]
  omega

lemma eraseGate_output_lt (n : ℕ) (C : Circuit) (m p : ℕ)
    (hm : m < C.gates.length) (hp : p < n + m) (hout : C.output < n + C.gates.length) :
    (eraseGate n C m p).output < n + (eraseGate n C m p).gates.length := by
  rw [eraseGate_gates_length n C m p hm]
  simp only [eraseGate, hm, ↓reduceIte]
  unfold eraseRedirect
  split_ifs <;> omega

lemma eraseGate_getElem_lt (n : ℕ) (C : Circuit) (m p j : ℕ)
    (hm : m < C.gates.length) (hjm : j < m) (hj : j < (eraseGate n C m p).gates.length) :
    (eraseGate n C m p).gates[j] = C.gates[j]'(by omega) := by
  have htake : j < (C.gates.take m).length := by simp; omega
  simp only [eraseGate, hm, ↓reduceIte]
  rw [List.getElem_append_left htake, List.getElem_take]

lemma eraseGate_getElem_ge (n : ℕ) (C : Circuit) (m p j : ℕ)
    (hm : m < C.gates.length) (hmj : m ≤ j) (hj : j < (eraseGate n C m p).gates.length) :
    (eraseGate n C m p).gates[j] =
      ⟨(C.gates[j + 1]'(by have := eraseGate_gates_length n C m p hm; omega)).op,
        (C.gates[j + 1]'(by have := eraseGate_gates_length n C m p hm; omega)).inputs.map
          (eraseRedirect n m p)⟩ := by
  have hlen := eraseGate_gates_length n C m p hm
  have htake : (C.gates.take m).length = m := by simp; omega
  have hidx : m + 1 + (j - m) = j + 1 := by omega
  simp only [eraseGate, hm, ↓reduceIte]
  rw [List.getElem_append_right (by omega)]
  simp only [htake, List.getElem_map, List.getElem_drop, hidx]

lemma eraseGate_isAO2 (n : ℕ) (C : Circuit) (m p : ℕ)
    (hAO : IsAO2 n C) (hm : m < C.gates.length) (hp : p < n + m) :
    IsAO2 n (eraseGate n C m p) := by
  rcases hAO with ⟨hAO_op, hRB, hLen2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [eraseGate, hm, ↓reduceIte, List.mem_append, List.mem_map] at hg
    rcases hg with h1 | ⟨g0, hg0, rfl⟩
    · exact hAO_op g (List.mem_of_mem_take h1)
    · exact hAO_op g0 (List.mem_of_mem_drop hg0)
  · intro j hj i hi
    rw [gateAt_eq_getElem _ j hj] at hi
    by_cases hjm : j < m
    · rw [eraseGate_getElem_lt n C m p j hm hjm hj] at hi
      have := hRB j (by omega) i
      rw [gateAt_eq_getElem C j (by omega)] at this
      exact this hi
    · have hmj : m ≤ j := by omega
      have hlen := eraseGate_gates_length n C m p hm
      rw [eraseGate_getElem_ge n C m p j hm hmj hj] at hi
      simp only [List.mem_map] at hi
      rcases hi with ⟨u, hu, rfl⟩
      have hu_lt : u < n + (j + 1) := by
        have := hRB (j + 1) (by omega) u
        rw [gateAt_eq_getElem C (j + 1) (by omega)] at this
        exact this hu
      exact eraseRedirect_lt n m p j u hp hmj hu_lt
  · intro g hg
    simp only [eraseGate, hm, ↓reduceIte, List.mem_append, List.mem_map] at hg
    rcases hg with h1 | ⟨g0, hg0, rfl⟩
    · exact hLen2 g (List.mem_of_mem_take h1)
    · simp [hLen2 g0 (List.mem_of_mem_drop hg0)]

lemma liftAt_isAO2 (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m) :
    IsAO2 n (liftAt n C m p h) := by
  have hE := eraseGate_isAO2 n C m p hAO hm hp
  have hEout := eraseGate_output_lt n C m p hm hp hout
  have hElen := eraseGate_gates_length n C m p hm
  rcases hE with ⟨hE_op, hE_RB, hE_len2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [liftAt, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hE_op g hg
    · exact Or.inr rfl
  · intro j hj i hi
    rw [gateAt_eq_getElem _ j hj] at hi
    simp only [liftAt, List.length_append, List.length_singleton] at hj
    by_cases hjE : j < (eraseGate n C m p).gates.length
    · have hg : (liftAt n C m p h).gates[j] = (eraseGate n C m p).gates[j] := by
        simp only [liftAt]
        rw [List.getElem_append_left hjE]
      rw [hg] at hi
      have := hE_RB j hjE i
      rw [gateAt_eq_getElem _ j hjE] at this
      exact this hi
    · have hj_eq : j = (eraseGate n C m p).gates.length := by omega
      have hg : (liftAt n C m p h).gates[j] = ⟨GateOp.or, [(eraseGate n C m p).output, h]⟩ := by
        simp only [liftAt]
        rw [List.getElem_append_right (by omega)]
        have : j - (eraseGate n C m p).gates.length = 0 := by omega
        simp [this]
      rw [hg] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · omega
      · omega
  · intro g hg
    simp only [liftAt, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hE_len2 g hg
    · rfl

lemma eraseGate_wires_prefix (n : ℕ) (C : Circuit) (m p : ℕ)
    (hm : m < C.gates.length) (x : List Bool) (hx : x.length = n)
    (k : ℕ) (hk : k < n + m) :
    ((eraseGate n C m p).wires x).getD k false = (C.wires x).getD k false := by
  change (evalGates (eraseGate n C m p).gates x).getD k false = (evalGates C.gates x).getD k false
  have hC : C.gates = C.gates.take m ++ C.gates.drop m := (List.take_append_drop m C.gates).symm
  have hE : (eraseGate n C m p).gates = C.gates.take m ++
      (C.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) := by
    simp [eraseGate, hm]
  have hlen : (evalGates (C.gates.take m) x).length = n + m := by
    rw [evalGates_length, hx, List.length_take]
    omega
  have hl : (evalGates (eraseGate n C m p).gates x).getD k false =
      (evalGates (C.gates.take m) x).getD k false := by
    rw [hE, evalGates_append]
    exact evalGates_getD_lt _ _ k (by omega)
  have hr : (evalGates C.gates x).getD k false =
      (evalGates (C.gates.take m) x).getD k false := by
    conv_lhs => rw [hC, evalGates_append]
    exact evalGates_getD_lt _ _ k (by omega)
  rw [hl, hr]

lemma liftAt_wires_lt (n : ℕ) (C : Circuit) (m p h : ℕ)
    (x : List Bool) (hx : x.length = n)
    (k : ℕ) (hk : k < n + (eraseGate n C m p).gates.length) :
    ((liftAt n C m p h).wires x).getD k false = ((eraseGate n C m p).wires x).getD k false := by
  change (evalGates ((eraseGate n C m p).gates ++ _) x).getD k false =
    (evalGates (eraseGate n C m p).gates x).getD k false
  rw [evalGates_append]
  have hlen : (evalGates (eraseGate n C m p).gates x).length = n + (eraseGate n C m p).gates.length := by
    rw [evalGates_length, hx]
  exact evalGates_getD_lt _ _ k (by omega)

lemma liftAt_eval_formula (n : ℕ) (C : Circuit) (m p h : ℕ)
    (x : List Bool) (hx : x.length = n) :
    (liftAt n C m p h).eval x =
      ((eraseGate n C m p).eval x || ((eraseGate n C m p).wires x).getD h false) := by
  unfold Circuit.eval liftAt
  change (evalGates ((eraseGate n C m p).gates ++ [⟨GateOp.or, [(eraseGate n C m p).output, h]⟩]) x).getD
      (n + (eraseGate n C m p).gates.length) false =
    ((evalGates (eraseGate n C m p).gates x).getD (eraseGate n C m p).output false ||
      (evalGates (eraseGate n C m p).gates x).getD h false)
  rw [evalGates_append]
  set wE := evalGates (eraseGate n C m p).gates x
  have hwE : wE.length = n + (eraseGate n C m p).gates.length := by
    rw [evalGates_length, hx]
  simp only [evalGates, List.foldl_cons, List.foldl_nil]
  rw [← hwE]
  simp [List.getD_eq_getElem?_getD, GateOp.eval]

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f g : ℕ → Bool) (hfg : ∀ u ∈ l, f u = true → g u = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro hf b hb
    rcases hb with ⟨u, hu, rfl⟩
    exact hfg u hu (hf (f u) ⟨u, hu, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨u, hu, rfl⟩, hfu⟩
    exact ⟨g u, ⟨u, hu, rfl⟩, hfg u hu hfu⟩

lemma gate_m_val (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hRB : ReadsBack n C) (hm : m < C.gates.length)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (x : List Bool) (hx : x.length = n) :
    (C.wires x).getD (n + m) false = ((C.wires x).getD p false || (C.wires x).getD h false) := by
  rw [wires_getD_gate n C hRB x hx m hm]
  have hg : C.gates[m] = ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m] = ⟨GateOp.or, [h, p]⟩ := by
    rcases hgate with h1 | h1
    · left; simpa [hm] using h1
    · right; simpa [hm] using h1
  rcases hg with h1 | h1
  · rw [h1]; simp [GateOp.eval]
  · rw [h1]; simp [GateOp.eval, Bool.or_comm]

lemma eraseGate_wires_le (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hAO : IsAO2 n C) (hm : m < C.gates.length) (hp : p < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (x : List Bool) (hx : x.length = n) :
    ∀ k < n + (eraseGate n C m p).gates.length,
      ((eraseGate n C m p).wires x).getD k false = true →
      (C.wires x).getD (if k < n + m then k else k + 1) false = true := by
  have hEAO := eraseGate_isAO2 n C m p hAO hm hp
  have hElen := eraseGate_gates_length n C m p hm
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk htrue
    by_cases hkm : k < n + m
    · simp only [hkm, ↓reduceIte]
      rwa [eraseGate_wires_prefix n C m p hm x hx k hkm] at htrue
    · simp only [hkm, ↓reduceIte]
      set j := k - n
      have hkj : k = n + j := by omega
      have hmj : m ≤ j := by omega
      have hjE : j < (eraseGate n C m p).gates.length := by omega
      have hjC : j + 1 < C.gates.length := by omega
      rw [hkj] at htrue ⊢
      have hkj1 : n + j + 1 = n + (j + 1) := by omega
      rw [hkj1]
      rw [wires_getD_gate n (eraseGate n C m p) hEAO.2.1 x hx j hjE] at htrue
      rw [eraseGate_getElem_ge n C m p j hm hmj hjE] at htrue
      rw [List.map_map] at htrue
      rw [wires_getD_gate n C hAO.2.1 x hx (j + 1) hjC]
      have hop : (C.gates[j + 1]).op = GateOp.and ∨ (C.gates[j + 1]).op = GateOp.or :=
        hAO.1 _ (List.getElem_mem hjC)
      refine gateOp_eval_mono _ hop _ _ _ ?_ htrue
      intro u hu huE
      have hu_lt : u < n + (j + 1) := by
        have := hAO.2.1 (j + 1) hjC u
        rw [gateAt_eq_getElem C (j + 1) hjC] at this
        exact this hu
      simp only [Function.comp_apply] at huE
      unfold eraseRedirect at huE
      split_ifs at huE with heq hgt
      · rw [heq, gate_m_val n C m p h hAO.2.1 hm hgate x hx]
        rw [eraseGate_wires_prefix n C m p hm x hx p hp] at huE
        rw [huE]
        rfl
      · have hstep := ih (u - 1) (by omega) (by omega) huE
        have hnotlt : ¬ (u - 1 < n + m) := by omega
        simp only [hnotlt, ↓reduceIte] at hstep
        have hu1 : u - 1 + 1 = u := by omega
        rwa [hu1] at hstep
      · have hult : u < n + m := by omega
        rwa [eraseGate_wires_prefix n C m p hm x hx u hult] at huE

lemma eraseGate_wires_eq_of_h_false (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hAO : IsAO2 n C) (hm : m < C.gates.length) (hp : p < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (x : List Bool) (hx : x.length = n) (hfalse : (C.wires x).getD h false = false) :
    ∀ k < n + (eraseGate n C m p).gates.length,
      ((eraseGate n C m p).wires x).getD k false =
      (C.wires x).getD (if k < n + m then k else k + 1) false := by
  have hEAO := eraseGate_isAO2 n C m p hAO hm hp
  have hElen := eraseGate_gates_length n C m p hm
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    by_cases hkm : k < n + m
    · simp only [hkm, ↓reduceIte]
      exact eraseGate_wires_prefix n C m p hm x hx k hkm
    · simp only [hkm, ↓reduceIte]
      set j := k - n
      have hkj : k = n + j := by omega
      have hmj : m ≤ j := by omega
      have hjE : j < (eraseGate n C m p).gates.length := by omega
      have hjC : j + 1 < C.gates.length := by omega
      rw [hkj]
      have hkj1 : n + j + 1 = n + (j + 1) := by omega
      rw [hkj1]
      rw [wires_getD_gate n (eraseGate n C m p) hEAO.2.1 x hx j hjE]
      rw [eraseGate_getElem_ge n C m p j hm hmj hjE]
      rw [List.map_map]
      rw [wires_getD_gate n C hAO.2.1 x hx (j + 1) hjC]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hu_lt : u < n + (j + 1) := by
        have := hAO.2.1 (j + 1) hjC u
        rw [gateAt_eq_getElem C (j + 1) hjC] at this
        exact this hu
      simp only [Function.comp_apply]
      unfold eraseRedirect
      split_ifs with heq hgt
      · rw [heq, gate_m_val n C m p h hAO.2.1 hm hgate x hx, hfalse, Bool.or_false]
        exact eraseGate_wires_prefix n C m p hm x hx p hp
      · have hstep := ih (u - 1) (by omega) (by omega)
        have hnotlt : ¬ (u - 1 < n + m) := by omega
        simp only [hnotlt, ↓reduceIte] at hstep
        have hu1 : u - 1 + 1 = u := by omega
        rwa [hu1] at hstep
      · have hult : u < n + m := by omega
        exact eraseGate_wires_prefix n C m p hm x hx u hult

lemma liftAt_eval_eq (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (hBelowH : WireBelowOutput n C h) (v : Fin n → Bool) :
    (liftAt n C m p h).eval (List.ofFn v) = C.eval (List.ofFn v) := by
  have hx : (List.ofFn v).length = n := List.length_ofFn
  rw [liftAt_eval_formula n C m p h (List.ofFn v) hx]
  rw [eraseGate_wires_prefix n C m p hm (List.ofFn v) hx h hh]
  cases hb : (C.wires (List.ofFn v)).getD h false
  · rw [Bool.or_false]
    unfold Circuit.eval
    have hEout : (eraseGate n C m p).output = eraseRedirect n m p C.output := by
      simp [eraseGate, hm]
    rw [hEout]
    have hElen := eraseGate_gates_length n C m p hm
    unfold eraseRedirect
    split_ifs with heq hgt
    · rw [heq, gate_m_val n C m p h hAO.2.1 hm hgate (List.ofFn v) hx, hb, Bool.or_false]
      exact eraseGate_wires_prefix n C m p hm (List.ofFn v) hx p hp
    · have hstep := eraseGate_wires_eq_of_h_false n C m p h hAO hm hp hgate
        (List.ofFn v) hx hb (C.output - 1) (by omega)
      have hnotlt : ¬ (C.output - 1 < n + m) := by omega
      simp only [hnotlt, ↓reduceIte] at hstep
      have ho1 : C.output - 1 + 1 = C.output := by omega
      rwa [ho1] at hstep
    · have holt : C.output < n + m := by omega
      exact eraseGate_wires_prefix n C m p hm (List.ofFn v) hx C.output holt
  · rw [Bool.or_true]
    exact (hBelowH v hb).symm

noncomputable def belowCount (n : ℕ) (C : Circuit) : ℕ :=
  ((Finset.range C.gates.length).filter (fun j => WireBelowOutput n C (n + j))).card

lemma belowCount_le (n : ℕ) (C : Circuit) : belowCount n C ≤ C.gates.length := by
  unfold belowCount
  calc ((Finset.range C.gates.length).filter _).card
      ≤ (Finset.range C.gates.length).card := Finset.card_filter_le _ _
    _ = C.gates.length := Finset.card_range _

lemma belowCount_lt_liftAt (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (hBelowH : WireBelowOutput n C h) (hNotBelowP : ¬ WireBelowOutput n C p) :
    belowCount n C < belowCount n (liftAt n C m p h) := by
  classical
  have hElen : (eraseGate n C m p).gates.length = C.gates.length - 1 :=
    eraseGate_gates_length n C m p hm
  have hC'len : (liftAt n C m p h).gates.length = C.gates.length :=
    liftAt_gates_length n C m p h hm
  have heval : ∀ v : Fin n → Bool, (liftAt n C m p h).eval (List.ofFn v) = C.eval (List.ofFn v) :=
    liftAt_eval_eq n C m p h hAO hout hm hp hh hgate hBelowH
  set S := (Finset.range C.gates.length).filter (fun j => WireBelowOutput n C (n + j))
  set S' := (Finset.range (liftAt n C m p h).gates.length).filter
    (fun j => WireBelowOutput n (liftAt n C m p h) (n + j))
  have hm_not : m ∉ S := by
    intro hmS
    have hBm : WireBelowOutput n C (n + m) := (Finset.mem_filter.mp hmS).2
    apply hNotBelowP
    intro v hpv
    apply hBm v
    rw [gate_m_val n C m p h hAO.2.1 hm hgate (List.ofFn v) List.length_ofFn, hpv]
    rfl
  have hlast_mem : (eraseGate n C m p).gates.length ∈ S' := by
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    intro v hv
    exact hv
  let f : ℕ → ℕ := fun j => if j < m then j else j - 1
  have hsub : S.image f ⊆ S'.erase (eraseGate n C m p).gates.length := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨j, hjS, rfl⟩
    have hj_ne : j ≠ m := fun heq => hm_not (heq ▸ hjS)
    rcases Finset.mem_filter.mp hjS with ⟨hj_rng, hBj⟩
    have hj_lt : j < C.gates.length := Finset.mem_range.mp hj_rng
    rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
    by_cases hjm : j < m
    · simp only [f, hjm, ↓reduceIte]
      refine ⟨by omega, by omega, ?_⟩
      intro v hv
      rw [heval v]
      apply hBj v
      rw [liftAt_wires_lt n C m p h (List.ofFn v) List.length_ofFn (n + j) (by omega)] at hv
      rwa [eraseGate_wires_prefix n C m p hm (List.ofFn v) List.length_ofFn (n + j) (by omega)] at hv
    · simp only [f, hjm, ↓reduceIte]
      refine ⟨by omega, by omega, ?_⟩
      intro v hv
      rw [heval v]
      apply hBj v
      rw [liftAt_wires_lt n C m p h (List.ofFn v) List.length_ofFn (n + (j - 1)) (by omega)] at hv
      have hle := eraseGate_wires_le n C m p h hAO hm hp hgate
        (List.ofFn v) List.length_ofFn (n + (j - 1)) (by omega) hv
      have hnotlt : ¬ (n + (j - 1) < n + m) := by omega
      simp only [hnotlt, ↓reduceIte] at hle
      have hj1 : n + (j - 1) + 1 = n + j := by omega
      rwa [hj1] at hle
  have hinj : Set.InjOn f (S : Set ℕ) := by
    intro j1 hj1 j2 hj2 hfeq
    have h1ne : j1 ≠ m := fun heq => hm_not (heq ▸ hj1)
    have h2ne : j2 ≠ m := fun heq => hm_not (heq ▸ hj2)
    simp only [f] at hfeq
    split_ifs at hfeq <;> omega
  have hcard1 : S.card = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
  have hcard2 : (S.image f).card ≤ (S'.erase (eraseGate n C m p).gates.length).card :=
    Finset.card_le_card hsub
  have hcard3 : (S'.erase (eraseGate n C m p).gates.length).card + 1 = S'.card :=
    Finset.card_erase_add_one hlast_mem
  show S.card < S'.card
  omega

end LiftNormalize

lemma liftNormalize : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output < x1 + x2.gates.length → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), Relation.ReflTransGen (PEqualNP.CircuitMoves.Lift x1) x2 x5 ∧ ∀ x6 < x5.gates.length, ∀ (x8 x9 : ℕ), x5.gates[x6]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x8, x9] : PEqualNP.CircuitLowerBounds.Gate } → (x1 ≤ x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8) ∧ (x1 ≤ x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9) := by
  intro n C hAO hout
  have main : ∀ k : ℕ, ∀ C0 : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 n C0 →
      C0.output < n + C0.gates.length →
      C0.gates.length - PEqualNP.Outside.L_meta_2583.LiftNormalize.belowCount n C0 = k →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        Relation.ReflTransGen (PEqualNP.CircuitMoves.Lift n) C0 C' ∧
        ∀ m < C'.gates.length, ∀ a b : ℕ,
          C'.gates[m]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] } →
          (n ≤ b → PEqualNP.CircuitMoves.WireBelowOutput n C' b → PEqualNP.CircuitMoves.WireBelowOutput n C' a) ∧
          (n ≤ a → PEqualNP.CircuitMoves.WireBelowOutput n C' a → PEqualNP.CircuitMoves.WireBelowOutput n C' b) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro C0 hAO0 hout0 hk0
      by_cases hNF : ∀ m < C0.gates.length, ∀ a b : ℕ,
          C0.gates[m]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] } →
          (n ≤ b → PEqualNP.CircuitMoves.WireBelowOutput n C0 b → PEqualNP.CircuitMoves.WireBelowOutput n C0 a) ∧
          (n ≤ a → PEqualNP.CircuitMoves.WireBelowOutput n C0 a → PEqualNP.CircuitMoves.WireBelowOutput n C0 b)
      · exact ⟨C0, Relation.ReflTransGen.refl, hNF⟩
      · push Not at hNF
        rcases hNF with ⟨m, hm, a, b, hgate, hbad⟩
        have ha_lt : a < n + m := by
          have := hAO0.2.1 m hm a
          rw [PEqualNP.Outside.L_meta_2583.LiftNormalize.gateAt_eq_getElem C0 m hm] at this
          have hgm : C0.gates[m] = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] } := by
            simpa [hm] using hgate
          rw [hgm] at this
          exact this (by simp)
        have hb_lt : b < n + m := by
          have := hAO0.2.1 m hm b
          rw [PEqualNP.Outside.L_meta_2583.LiftNormalize.gateAt_eq_getElem C0 m hm] at this
          have hgm : C0.gates[m] = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] } := by
            simpa [hm] using hgate
          rw [hgm] at this
          exact this (by simp)
        have hstep : ∃ p h : ℕ, p < n + m ∧ h < n + m ∧ n ≤ h ∧
            (C0.gates[m]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [p, h] } ∨
              C0.gates[m]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [h, p] }) ∧
            PEqualNP.CircuitMoves.WireBelowOutput n C0 h ∧
            ¬ PEqualNP.CircuitMoves.WireBelowOutput n C0 p := by
          by_cases h1 : n ≤ b → PEqualNP.CircuitMoves.WireBelowOutput n C0 b →
              PEqualNP.CircuitMoves.WireBelowOutput n C0 a
          · rcases hbad h1 with ⟨hna, hBa, hNb⟩
            exact ⟨b, a, hb_lt, ha_lt, hna, Or.inr hgate, hBa, hNb⟩
          · push Not at h1
            rcases h1 with ⟨hnb, hBb, hNa⟩
            exact ⟨a, b, ha_lt, hb_lt, hnb, Or.inl hgate, hBb, hNa⟩
        rcases hstep with ⟨p, h, hp, hh, hnh, hgm, hBh, hNp⟩
        have hLift : PEqualNP.CircuitMoves.Lift n C0 (PEqualNP.CircuitMoves.liftAt n C0 m p h) :=
          ⟨m, hm, p, hp, h, hh, hnh, hgm, hBh, rfl⟩
        have hAO1 := PEqualNP.Outside.L_meta_2583.LiftNormalize.liftAt_isAO2 n C0 m p h hAO0 hout0 hm hp hh
        have hlen1 := PEqualNP.Outside.L_meta_2583.LiftNormalize.liftAt_gates_length n C0 m p h hm
        have hElen := PEqualNP.Outside.L_meta_2583.LiftNormalize.eraseGate_gates_length n C0 m p hm
        have hout1 : (PEqualNP.CircuitMoves.liftAt n C0 m p h).output <
            n + (PEqualNP.CircuitMoves.liftAt n C0 m p h).gates.length := by
          change n + (PEqualNP.CircuitMoves.eraseGate n C0 m p).gates.length <
            n + (PEqualNP.CircuitMoves.liftAt n C0 m p h).gates.length
          omega
        have hlt := PEqualNP.Outside.L_meta_2583.LiftNormalize.belowCount_lt_liftAt n C0 m p h hAO0 hout0 hm hp hh hgm hBh hNp
        have hle1 := PEqualNP.Outside.L_meta_2583.LiftNormalize.belowCount_le n (PEqualNP.CircuitMoves.liftAt n C0 m p h)
        have hk1 : (PEqualNP.CircuitMoves.liftAt n C0 m p h).gates.length -
            PEqualNP.Outside.L_meta_2583.LiftNormalize.belowCount n (PEqualNP.CircuitMoves.liftAt n C0 m p h) < k := by
          omega
        obtain ⟨C', hR, hNF'⟩ := ih _ hk1 (PEqualNP.CircuitMoves.liftAt n C0 m p h) hAO1 hout1 rfl
        exact ⟨C', Relation.ReflTransGen.head hLift hR, hNF'⟩
  exact main _ C hAO hout rfl


namespace BlockSeparate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.CircuitMoves

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wireStep_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl wireStep acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wireStep_prefix (gs : List Gate) (acc : List Bool) (w : ℕ) (hw : w < acc.length) :
    (gs.foldl wireStep acc).getD w false = acc.getD w false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hw' : w < (wireStep acc g).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (wireStep acc g) hw']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_left hw]

lemma gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

lemma wireValue_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    PEqualNP.BlindGate.wireValue C n x w = x ⟨w, hw⟩ := by
  unfold PEqualNP.BlindGate.wireValue Circuit.wires
  have hw' : w < (List.ofFn x).length := by simp [hw]
  have h1 := foldl_wireStep_prefix C.gates (List.ofFn x) w hw'
  change (C.gates.foldl wireStep (List.ofFn x)).getD w false = x ⟨w, hw⟩
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw']
  simp

lemma wireValue_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length) (hRB : ReadsBack n C) :
    PEqualNP.BlindGate.wireValue C n x (n + k) =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun u => PEqualNP.BlindGate.wireValue C n x u) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take k).foldl wireStep (List.ofFn x) with hacc
  have hacc_len : acc.length = n + k := by
    rw [hacc, foldl_wireStep_length, List.length_ofFn, List.length_take]
    omega
  have hpref : ∀ u < n + k, PEqualNP.BlindGate.wireValue C n x u = acc.getD u false := by
    intro u hu
    unfold PEqualNP.BlindGate.wireValue Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD u false = acc.getD u false
    conv_lhs => rw [← List.take_append_drop k C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_wireStep_prefix (C.gates.drop k) acc u (by omega)
  have hval : PEqualNP.BlindGate.wireValue C n x (n + k) =
      C.gates[k].op.eval (C.gates[k].inputs.map fun u => acc.getD u false) := by
    unfold PEqualNP.BlindGate.wireValue Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD (n + k) false = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : n + k < (wireStep acc C.gates[k]).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_wireStep_prefix (C.gates.drop (k + 1)) (wireStep acc C.gates[k]) (n + k) hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_right (by omega : acc.length ≤ n + k),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hval, gateAt_eq_getElem C k hk]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [← gateAt_eq_getElem C k hk] at hu
  exact (hpref u (hRB k hk u hu)).symm

lemma list_eq_two {α : Type} {l : List α} (h : l.length = 2) : ∃ a b, l = [a, b] := by
  cases l with
  | nil => simp at h
  | cons a t =>
    cases t with
    | nil => simp at h
    | cons b t2 =>
      cases t2 with
      | nil => exact ⟨a, b, rfl⟩
      | cons _ _ => simp at h

lemma gate_inputs_two (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, (gateAt C j).inputs = [a, b] ∧ a < n + j ∧ b < n + j := by
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [gateAt_eq_getElem C j hj]
    exact hAO.2.2 C.gates[j] (List.getElem_mem hj)
  rcases list_eq_two hlen with ⟨a, b, hab⟩
  refine ⟨a, b, hab, ?_, ?_⟩
  · exact hAO.2.1 j hj a (by simp [hab])
  · exact hAO.2.1 j hj b (by simp [hab])

lemma wireValue_and_pair (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (j a b : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and)
    (hin : (gateAt C j).inputs = [a, b]) (x : Fin n → Bool) :
    PEqualNP.BlindGate.wireValue C n x (n + j) =
      (PEqualNP.BlindGate.wireValue C n x a && PEqualNP.BlindGate.wireValue C n x b) := by
  rw [wireValue_gate n C x j hj hRB, hop, hin]
  simp [GateOp.eval]

lemma wireValue_or_pair (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (j a b : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or)
    (hin : (gateAt C j).inputs = [a, b]) (x : Fin n → Bool) :
    PEqualNP.BlindGate.wireValue C n x (n + j) =
      (PEqualNP.BlindGate.wireValue C n x a || PEqualNP.BlindGate.wireValue C n x b) := by
  rw [wireValue_gate n C x j hj hRB, hop, hin]
  simp [GateOp.eval]

def keepList (p : ℕ → Bool) (m : ℕ) : List ℕ :=
  (List.range m).filter p

def rankOf (p : ℕ → Bool) (k : ℕ) : ℕ :=
  (keepList p k).length

lemma keepList_succ (p : ℕ → Bool) (m : ℕ) :
    keepList p (m + 1) = keepList p m ++ if p m then [m] else [] := by
  unfold keepList
  rw [List.range_succ, List.filter_append]
  cases hp : p m <;> simp [hp]

lemma rankOf_succ (p : ℕ → Bool) (m : ℕ) :
    rankOf p (m + 1) = rankOf p m + if p m then 1 else 0 := by
  unfold rankOf
  rw [keepList_succ, List.length_append]
  cases p m <;> simp

lemma rankOf_mono (p : ℕ → Bool) {a b : ℕ} (hab : a ≤ b) :
    rankOf p a ≤ rankOf p b := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha
    exact le_refl _
  | succ b ih =>
    by_cases hlt : a ≤ b
    · have h1 := ih hlt
      rw [rankOf_succ]
      omega
    · have ha : a = b + 1 := by omega
      subst ha
      exact le_refl _

lemma rankOf_lt_of_lt (p : ℕ → Bool) {a b : ℕ} (hab : a < b) (ha : p a = true) :
    rankOf p a < rankOf p b := by
  have h1 : rankOf p a + 1 = rankOf p (a + 1) := by
    rw [rankOf_succ, ha]
    simp
  have h2 : rankOf p (a + 1) ≤ rankOf p b := rankOf_mono p hab
  omega

lemma keepList_getElem_props (p : ℕ → Bool) (m : ℕ) :
    ∀ k (hk : k < (keepList p m).length),
      (keepList p m)[k] < m ∧ p (keepList p m)[k] = true ∧ rankOf p (keepList p m)[k] = k := by
  induction m with
  | zero =>
    intro k hk
    simp [keepList] at hk
  | succ m ih =>
    intro k hk
    cases hpm : p m
    · have hEq : keepList p (m + 1) = keepList p m := by
        rw [keepList_succ, hpm]
        simp
      have hk' : k < (keepList p m).length := by simpa [hEq] using hk
      have h1 := ih k hk'
      have hget : (keepList p (m + 1))[k] = (keepList p m)[k] := by
        simp [hEq]
      rw [hget]
      exact ⟨by omega, h1.2.1, h1.2.2⟩
    · have hEq : keepList p (m + 1) = keepList p m ++ [m] := by
        rw [keepList_succ, hpm]
        simp
      have hk' : k < (keepList p m).length + 1 := by
        simpa [hEq] using hk
      by_cases hlt : k < (keepList p m).length
      · have h1 := ih k hlt
        have hget : (keepList p (m + 1))[k] = (keepList p m)[k] := by
          simp [hEq, List.getElem_append_left hlt]
        rw [hget]
        exact ⟨by omega, h1.2.1, h1.2.2⟩
      · have hkeq : k = (keepList p m).length := by omega
        have hget : (keepList p (m + 1))[k] = m := by
          simp [hEq, hkeq]
        rw [hget]
        exact ⟨by omega, hpm, by unfold rankOf; omega⟩

lemma keepList_getElem_rankOf (p : ℕ → Bool) (m : ℕ) :
    ∀ j < m, p j = true →
      ∃ hlt : rankOf p j < (keepList p m).length, (keepList p m)[rankOf p j] = j := by
  induction m with
  | zero =>
    intro j hj
    omega
  | succ m ih =>
    intro j hj hpj
    cases hpm : p m
    · have hEq : keepList p (m + 1) = keepList p m := by
        rw [keepList_succ, hpm]
        simp
      have hjm : j < m := by
        by_contra hge
        have : j = m := by omega
        subst this
        rw [hpm] at hpj
        cases hpj
      obtain ⟨hlt, hget⟩ := ih j hjm hpj
      refine ⟨by simpa [hEq] using hlt, ?_⟩
      simp [hEq, hget]
    · have hEq : keepList p (m + 1) = keepList p m ++ [m] := by
        rw [keepList_succ, hpm]
        simp
      by_cases hjm : j < m
      · obtain ⟨hlt, hget⟩ := ih j hjm hpj
        refine ⟨by simp [hEq]; omega, ?_⟩
        simp [hEq, List.getElem_append_left hlt, hget]
      · have hjeq : j = m := by omega
        subst hjeq
        have hr : rankOf p j = (keepList p j).length := rfl
        refine ⟨by simp [hEq, hr], ?_⟩
        simp [hEq, hr]

lemma rankOf_add_filter_card (p : ℕ → Bool) (m : ℕ) :
    rankOf p m + ((Finset.range m).filter (fun j => p j = false)).card = m := by
  induction m with
  | zero => simp [rankOf, keepList]
  | succ m ih =>
    rw [rankOf_succ, Finset.range_add_one, Finset.filter_insert]
    cases hpm : p m
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      have hnot : m ∉ (Finset.range m).filter (fun j => p j = false) := by
        simp
      rw [Finset.card_insert_of_notMem hnot]
      omega
    · simp only [↓reduceIte, Bool.true_eq_false]
      omega

def isAndOp : GateOp → Bool
  | GateOp.and => true
  | _ => false

lemma isAndOp_eq_true_iff (op : GateOp) : isAndOp op = true ↔ op = GateOp.and := by
  cases op <;> simp [isAndOp]

def isTopAndB (n : ℕ) (C : Circuit) (j : ℕ) : Bool :=
  decide (j < C.gates.length) &&
  decide (WireBelowOutput n C (n + j)) &&
  isAndOp (gateAt C j).op &&
  (gateAt C j).inputs.all (fun u => !decide (WireBelowOutput n C u))

lemma isTopAndB_eq_true_iff (n : ℕ) (C : Circuit) (j : ℕ) :
    isTopAndB n C j = true ↔
      j < C.gates.length ∧ WireBelowOutput n C (n + j) ∧
      (gateAt C j).op = GateOp.and ∧
      ∀ u ∈ (gateAt C j).inputs, ¬ WireBelowOutput n C u := by
  unfold isTopAndB
  simp only [Bool.and_eq_true, decide_eq_true_eq, isAndOp_eq_true_iff, List.all_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, and_assoc]

lemma kept_downward_closed (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hNoIn : ∀ i < n, ¬ WireBelowOutput n C i)
    (hOr : ∀ j < C.size, ∀ (a b : ℕ),
      C.gates[j]? = some ⟨GateOp.or, [a, b]⟩ →
        (n ≤ b → WireBelowOutput n C b → WireBelowOutput n C a) ∧
        (n ≤ a → WireBelowOutput n C a → WireBelowOutput n C b))
    (j : ℕ) (hj : j < C.gates.length) (hnot : ¬ WireBelowOutput n C (n + j)) :
    ∀ u ∈ (gateAt C j).inputs, ¬ WireBelowOutput n C u := by
  obtain ⟨a, b, hab, _, _⟩ := gate_inputs_two n C hAO j hj
  have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    rw [gateAt_eq_getElem C j hj]
    exact hAO.1 C.gates[j] (List.getElem_mem hj)
  intro u hu
  rw [hab] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hop with hand | hor
  · intro hwu
    apply hnot
    intro x hx
    change PEqualNP.BlindGate.wireValue C n x (n + j) = true at hx
    rw [wireValue_and_pair n C hAO.2.1 j a b hj hand hab x] at hx
    rw [Bool.and_eq_true] at hx
    rcases hu with rfl | rfl
    · exact hwu x hx.1
    · exact hwu x hx.2
  · have hget : C.gates[j]? = some ⟨GateOp.or, [a, b]⟩ := by
      rw [List.getElem?_eq_getElem hj]
      congr 1
      have h1 : C.gates[j].op = GateOp.or := by rw [← gateAt_eq_getElem C j hj]; exact hor
      have h2 : C.gates[j].inputs = [a, b] := by rw [← gateAt_eq_getElem C j hj]; exact hab
      cases hcj : C.gates[j] with
      | mk gop ginputs =>
        rw [hcj] at h1 h2
        dsimp only at h1 h2
        rw [h1, h2]
    have horj := hOr j hj a b hget
    intro hwu
    have hboth : WireBelowOutput n C a ∧ WireBelowOutput n C b := by
      rcases hu with hEq | hEq
      · rw [hEq] at hwu
        have ha_ge : n ≤ a := by
          by_contra hlt
          exact hNoIn a (by omega) hwu
        exact ⟨hwu, horj.2 ha_ge hwu⟩
      · rw [hEq] at hwu
        have hb_ge : n ≤ b := by
          by_contra hlt
          exact hNoIn b (by omega) hwu
        exact ⟨horj.1 hb_ge hwu, hwu⟩
    apply hnot
    intro x hx
    change PEqualNP.BlindGate.wireValue C n x (n + j) = true at hx
    rw [wireValue_or_pair n C hAO.2.1 j a b hj hor hab x] at hx
    rw [Bool.or_eq_true] at hx
    rcases hx with hxa | hxb
    · exact hboth.1 x hxa
    · exact hboth.2 x hxb

lemma peel_below (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hNoIn : ∀ i < n, ¬ WireBelowOutput n C i)
    (below : Finset ℕ)
    (hbelow_def : below = (Finset.range C.gates.length).filter (fun j => WireBelowOutput n C (n + j))) :
    ∀ k : ℕ, ∀ S D : Finset ℕ,
      below.card - D.card ≤ k →
      S ⊆ below →
      D ⊆ below →
      Disjoint S D →
      S.card ≤ D.card + 1 →
      (∀ x : Fin n → Bool, circuitFun n C x = true →
        ∃ j ∈ S, PEqualNP.BlindGate.wireValue C n x (n + j) = true) →
      (∀ s ∈ S, isTopAndB n C s = false → ∀ d ∈ D, s < d) →
      ∃ S' D' : Finset ℕ,
        S' ⊆ below ∧
        D' ⊆ below ∧
        Disjoint S' D' ∧
        S'.card ≤ D'.card + 1 ∧
        (∀ j ∈ S', isTopAndB n C j = true) ∧
        (∀ x : Fin n → Bool, circuitFun n C x = true →
          ∃ j ∈ S', PEqualNP.BlindGate.wireValue C n x (n + j) = true) := by
  intro k
  induction k with
  | zero =>
    intro S D hk hS hD hDisj hCard hCov hOrd
    set bad := S.filter (fun j => isTopAndB n C j = false) with hbad_def
    by_cases hEmpty : bad = ∅
    · refine ⟨S, D, hS, hD, hDisj, hCard, ?_, hCov⟩
      intro j hj
      cases ht : isTopAndB n C j with
      | true => rfl
      | false =>
        have hmem : j ∈ bad := by
          rw [hbad_def, Finset.mem_filter]
          exact ⟨hj, ht⟩
        rw [hEmpty] at hmem
        exact absurd hmem (Finset.notMem_empty j)
    · have hne : bad.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
      obtain ⟨m, hm⟩ := hne
      rw [hbad_def, Finset.mem_filter] at hm
      have hmB : m ∈ below := hS hm.1
      have hmNotD : m ∉ D := Finset.disjoint_left.mp hDisj hm.1
      have hDlt : D.card < below.card := by
        have hsub : insert m D ⊆ below := Finset.insert_subset hmB hD
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem hmNotD] at h1
        omega
      omega
  | succ k ih =>
    intro S D hk hS hD hDisj hCard hCov hOrd
    set bad := S.filter (fun j => isTopAndB n C j = false) with hbad_def
    by_cases hEmpty : bad = ∅
    · refine ⟨S, D, hS, hD, hDisj, hCard, ?_, hCov⟩
      intro j hj
      cases ht : isTopAndB n C j with
      | true => rfl
      | false =>
        have hmem : j ∈ bad := by
          rw [hbad_def, Finset.mem_filter]
          exact ⟨hj, ht⟩
        rw [hEmpty] at hmem
        exact absurd hmem (Finset.notMem_empty j)
    · have hne : bad.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
      set m := bad.max' hne with hm_def
      have hm_bad : m ∈ bad := Finset.max'_mem bad hne
      rw [hbad_def, Finset.mem_filter] at hm_bad
      have hmS : m ∈ S := hm_bad.1
      have hmFalse : isTopAndB n C m = false := hm_bad.2
      have hmB : m ∈ below := hS hmS
      have hmNotD : m ∉ D := Finset.disjoint_left.mp hDisj hmS
      have hmProps : m < C.gates.length ∧ WireBelowOutput n C (n + m) := by
        rw [hbelow_def, Finset.mem_filter, Finset.mem_range] at hmB
        exact hmB
      have hm_lt_D : ∀ d ∈ D, m < d := hOrd m hmS hmFalse
      have hD'_card : (insert m D).card = D.card + 1 := Finset.card_insert_of_notMem hmNotD
      have hD'_sub : insert m D ⊆ below := Finset.insert_subset hmB hD
      have hk' : below.card - (insert m D).card ≤ k := by
        have hle := Finset.card_le_card hD'_sub
        omega
      obtain ⟨a, b, hab, ha_lt, hb_lt⟩ := gate_inputs_two n C hAO m hmProps.1
      have hop : (gateAt C m).op = GateOp.and ∨ (gateAt C m).op = GateOp.or := by
        rw [gateAt_eq_getElem C m hmProps.1]
        exact hAO.1 C.gates[m] (List.getElem_mem hmProps.1)
      rcases hop with hand | hor
      · have hex : ∃ u ∈ (gateAt C m).inputs, WireBelowOutput n C u := by
          by_contra hall
          push Not at hall
          have htrue : isTopAndB n C m = true := by
            rw [isTopAndB_eq_true_iff]
            exact ⟨hmProps.1, hmProps.2, hand, hall⟩
          rw [hmFalse] at htrue
          cases htrue
        obtain ⟨u, hu_mem, hu_below⟩ := hex
        have hu_lt : u < n + m := hAO.2.1 m hmProps.1 u hu_mem
        have hu_ge : n ≤ u := by
          by_contra hlt
          exact hNoIn u (by omega) hu_below
        set ju := u - n with hju_def
        have hju_lt : ju < m := by omega
        have hju_eq : n + ju = u := by omega
        have hjuB : ju ∈ below := by
          rw [hbelow_def, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, by rw [hju_eq]; exact hu_below⟩
        set S1 := insert ju (S.erase m) with hS1_def
        set D1 := insert m D with hD1_def
        apply ih S1 D1 hk'
        · intro s hs
          simp only [hS1_def, Finset.mem_insert, Finset.mem_erase] at hs
          rcases hs with rfl | ⟨_, hsS⟩
          · exact hjuB
          · exact hS hsS
        · exact hD'_sub
        · rw [Finset.disjoint_left]
          intro s hs hsD1
          simp only [hD1_def, Finset.mem_insert] at hsD1
          simp only [hS1_def, Finset.mem_insert, Finset.mem_erase] at hs
          rcases hs with hEqs | ⟨hne_m, hsS⟩
          · rcases hsD1 with hEqm | hdD
            · omega
            · have hlt_d := hm_lt_D s hdD
              omega
          · rcases hsD1 with hEqm | hdD
            · exact hne_m hEqm
            · exact Finset.disjoint_left.mp hDisj hsS hdD
        · have h1 : S1.card ≤ (S.erase m).card + 1 := Finset.card_insert_le ju (S.erase m)
          have h2 : (S.erase m).card = S.card - 1 := Finset.card_erase_of_mem hmS
          have h3 : 1 ≤ S.card := Finset.one_le_card.mpr ⟨m, hmS⟩
          rw [hD1_def, hD'_card]
          omega
        · intro x hfx
          obtain ⟨j, hjS, hjx⟩ := hCov x hfx
          by_cases hjm : j = m
          · rw [hjm] at hjx
            refine ⟨ju, ?_, ?_⟩
            · simp [hS1_def]
            · rw [hju_eq]
              rw [wireValue_and_pair n C hAO.2.1 m a b hmProps.1 hand hab x] at hjx
              rw [Bool.and_eq_true] at hjx
              rw [hab] at hu_mem
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_mem
              rcases hu_mem with rfl | rfl
              · exact hjx.1
              · exact hjx.2
          · exact ⟨j, by simp [hS1_def, hjm, hjS], hjx⟩
        · intro s hs hsFalse d hd
          have hm_le_d : m ≤ d := by
            simp only [hD1_def, Finset.mem_insert] at hd
            rcases hd with hEqm | hdD
            · omega
            · have := hm_lt_D d hdD; omega
          simp only [hS1_def, Finset.mem_insert, Finset.mem_erase] at hs
          rcases hs with hEqs | ⟨hne_m, hsS⟩
          · omega
          · have hs_bad : s ∈ bad := by
              rw [hbad_def, Finset.mem_filter]
              exact ⟨hsS, hsFalse⟩
            have hs_le : s ≤ m := Finset.le_max' bad s hs_bad
            omega
      · have ha_below : WireBelowOutput n C a := by
          intro x hxa
          apply hmProps.2 x
          change PEqualNP.BlindGate.wireValue C n x (n + m) = true
          change PEqualNP.BlindGate.wireValue C n x a = true at hxa
          rw [wireValue_or_pair n C hAO.2.1 m a b hmProps.1 hor hab x, hxa]
          simp
        have hb_below : WireBelowOutput n C b := by
          intro x hxb
          apply hmProps.2 x
          change PEqualNP.BlindGate.wireValue C n x (n + m) = true
          change PEqualNP.BlindGate.wireValue C n x b = true at hxb
          rw [wireValue_or_pair n C hAO.2.1 m a b hmProps.1 hor hab x, hxb]
          simp
        have ha_ge : n ≤ a := by
          by_contra hlt
          exact hNoIn a (by omega) ha_below
        have hb_ge : n ≤ b := by
          by_contra hlt
          exact hNoIn b (by omega) hb_below
        set ja := a - n with hja_def
        set jb := b - n with hjb_def
        have hja_lt : ja < m := by omega
        have hjb_lt : jb < m := by omega
        have hja_eq : n + ja = a := by omega
        have hjb_eq : n + jb = b := by omega
        have hjaB : ja ∈ below := by
          rw [hbelow_def, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, by rw [hja_eq]; exact ha_below⟩
        have hjbB : jb ∈ below := by
          rw [hbelow_def, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, by rw [hjb_eq]; exact hb_below⟩
        set S1 := insert ja (insert jb (S.erase m)) with hS1_def
        set D1 := insert m D with hD1_def
        apply ih S1 D1 hk'
        · intro s hs
          simp only [hS1_def, Finset.mem_insert, Finset.mem_erase] at hs
          rcases hs with rfl | rfl | ⟨_, hsS⟩
          · exact hjaB
          · exact hjbB
          · exact hS hsS
        · exact hD'_sub
        · rw [Finset.disjoint_left]
          intro s hs hsD1
          simp only [hD1_def, Finset.mem_insert] at hsD1
          simp only [hS1_def, Finset.mem_insert, Finset.mem_erase] at hs
          rcases hs with hEqa | hEqb | ⟨hne_m, hsS⟩
          · rcases hsD1 with hEqm | hdD
            · omega
            · have hlt_d := hm_lt_D s hdD; omega
          · rcases hsD1 with hEqm | hdD
            · omega
            · have hlt_d := hm_lt_D s hdD; omega
          · rcases hsD1 with hEqm | hdD
            · exact hne_m hEqm
            · exact Finset.disjoint_left.mp hDisj hsS hdD
        · have h1 : S1.card ≤ (insert jb (S.erase m)).card + 1 :=
            Finset.card_insert_le ja (insert jb (S.erase m))
          have h2 : (insert jb (S.erase m)).card ≤ (S.erase m).card + 1 :=
            Finset.card_insert_le jb (S.erase m)
          have h3 : (S.erase m).card = S.card - 1 := Finset.card_erase_of_mem hmS
          have h4 : 1 ≤ S.card := Finset.one_le_card.mpr ⟨m, hmS⟩
          rw [hD1_def, hD'_card]
          omega
        · intro x hfx
          obtain ⟨j, hjS, hjx⟩ := hCov x hfx
          by_cases hjm : j = m
          · rw [hjm] at hjx
            rw [wireValue_or_pair n C hAO.2.1 m a b hmProps.1 hor hab x] at hjx
            rw [Bool.or_eq_true] at hjx
            rcases hjx with hxa | hxb
            · exact ⟨ja, by simp [hS1_def], by rw [hja_eq]; exact hxa⟩
            · exact ⟨jb, by simp [hS1_def], by rw [hjb_eq]; exact hxb⟩
          · exact ⟨j, by simp [hS1_def, hjm, hjS], hjx⟩
        · intro s hs hsFalse d hd
          have hm_le_d : m ≤ d := by
            simp only [hD1_def, Finset.mem_insert] at hd
            rcases hd with hEqm | hdD
            · omega
            · have := hm_lt_D d hdD; omega
          simp only [hS1_def, Finset.mem_insert, Finset.mem_erase] at hs
          rcases hs with hEqa | hEqb | ⟨hne_m, hsS⟩
          · omega
          · omega
          · have hs_bad : s ∈ bad := by
              rw [hbad_def, Finset.mem_filter]
              exact ⟨hsS, hsFalse⟩
            have hs_le : s ≤ m := Finset.le_max' bad s hs_bad
            omega

lemma main_proof (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hOut : C.output < n + C.size)
    (hNoIn : ∀ i < n, ¬ WireBelowOutput n C i)
    (hOr : ∀ j < C.size, ∀ (a b : ℕ),
      C.gates[j]? = some ⟨GateOp.or, [a, b]⟩ →
        (n ≤ b → WireBelowOutput n C b → WireBelowOutput n C a) ∧
        (n ≤ a → WireBelowOutput n C a → WireBelowOutput n C b)) :
    ∃ (C' : Circuit) (pairs : List (ℕ × ℕ)),
      IsAO2 n C' ∧
      (∀ k < C'.size, ∃ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue C' n x (n + k) = true ∧ circuitFun n C x = false) ∧
      (∀ x : Fin n → Bool, circuitFun n C x = true ↔
        ∃ p ∈ pairs, PEqualNP.BlindGate.wireValue C' n x p.1 = true ∧
          PEqualNP.BlindGate.wireValue C' n x p.2 = true) ∧
      C'.size + 2 * pairs.length ≤ C.size + 1 := by
  let keepB : ℕ → Bool := fun j => !decide (WireBelowOutput n C (n + j))
  have hkeepB_true : ∀ j, keepB j = true ↔ ¬ WireBelowOutput n C (n + j) := by
    intro j
    simp [keepB]
  have hkeepB_false : ∀ j, keepB j = false ↔ WireBelowOutput n C (n + j) := by
    intro j
    simp [keepB]
  let wmap : ℕ → ℕ := fun w => if w < n then w else n + rankOf keepB (w - n)
  let kl := keepList keepB C.gates.length
  let C' : Circuit :=
    { gates := kl.map (fun j => ⟨(gateAt C j).op, (gateAt C j).inputs.map wmap⟩)
      output := 0 }
  have hC'_len : C'.gates.length = kl.length := by
    simp [C']
  have hDC : ∀ j < C.gates.length, keepB j = true →
      ∀ u ∈ (gateAt C j).inputs, ¬ WireBelowOutput n C u := by
    intro j hj hkj u hu
    exact kept_downward_closed n C hAO hNoIn hOr j hj ((hkeepB_true j).mp hkj) u hu
  have hC'_gateAt : ∀ k (hk : k < kl.length),
      gateAt C' k = ⟨(gateAt C kl[k]).op, (gateAt C kl[k]).inputs.map wmap⟩ := by
    intro k hk
    have hk' : k < C'.gates.length := by rw [hC'_len]; exact hk
    rw [gateAt_eq_getElem C' k hk']
    simp [C']
  have hC'_AO : IsAO2 n C' := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [C', List.mem_map] at hg
      obtain ⟨j, hj, rfl⟩ := hg
      have hj_lt : j < C.gates.length := by
        simp only [kl, keepList, List.mem_filter, List.mem_range] at hj
        exact hj.1
      rw [gateAt_eq_getElem C j hj_lt]
      exact hAO.1 C.gates[j] (List.getElem_mem hj_lt)
    · intro k hk w' hw'
      have hk_kl : k < kl.length := by rw [← hC'_len]; exact hk
      rw [hC'_gateAt k hk_kl] at hw'
      simp only [List.mem_map] at hw'
      obtain ⟨u, hu, rfl⟩ := hw'
      have hprops := keepList_getElem_props keepB C.gates.length k hk_kl
      have hj_lt : kl[k] < C.gates.length := hprops.1
      have hj_keep : keepB kl[k] = true := hprops.2.1
      have hj_rank : rankOf keepB kl[k] = k := hprops.2.2
      have hu_lt : u < n + kl[k] := hAO.2.1 kl[k] hj_lt u hu
      have hu_not : ¬ WireBelowOutput n C u := hDC kl[k] hj_lt hj_keep u hu
      by_cases hun : u < n
      · simp only [wmap, hun, ↓reduceIte]
        omega
      · simp only [wmap, hun, ↓reduceIte]
        have hku_true : keepB (u - n) = true := by
          rw [hkeepB_true]
          have heq : n + (u - n) = u := by omega
          rw [heq]
          exact hu_not
        have hlt_r : rankOf keepB (u - n) < rankOf keepB kl[k] :=
          rankOf_lt_of_lt keepB (by omega) hku_true
        omega
    · intro g hg
      simp only [C', List.mem_map] at hg
      obtain ⟨j, hj, rfl⟩ := hg
      have hj_lt : j < C.gates.length := by
        simp only [kl, keepList, List.mem_filter, List.mem_range] at hj
        exact hj.1
      simp only [List.length_map]
      rw [gateAt_eq_getElem C j hj_lt]
      exact hAO.2.2 C.gates[j] (List.getElem_mem hj_lt)
  have hWireEq : ∀ w < n + C.gates.length, ¬ WireBelowOutput n C w →
      ∀ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue C' n x (wmap w) = PEqualNP.BlindGate.wireValue C n x w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hnot x
      by_cases hwn : w < n
      · simp only [wmap, hwn, ↓reduceIte]
        rw [wireValue_input n C' x w hwn, wireValue_input n C x w hwn]
      · simp only [wmap, hwn, ↓reduceIte]
        set j := w - n with hj_def
        have hw_eq : n + j = w := by omega
        have hj_lt : j < C.gates.length := by omega
        have hj_keep : keepB j = true := by
          rw [hkeepB_true, hw_eq]
          exact hnot
        obtain ⟨hr_lt, hr_get⟩ := keepList_getElem_rankOf keepB C.gates.length j hj_lt hj_keep
        have hr_lt' : rankOf keepB j < C'.gates.length := by rw [hC'_len]; exact hr_lt
        rw [wireValue_gate n C' x (rankOf keepB j) hr_lt' hC'_AO.2.1]
        rw [hC'_gateAt (rankOf keepB j) hr_lt, hr_get]
        rw [← hw_eq, wireValue_gate n C x j hj_lt hAO.2.1]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hu_lt : u < n + j := hAO.2.1 j hj_lt u hu
        have hu_not : ¬ WireBelowOutput n C u := hDC j hj_lt hj_keep u hu
        exact ih u (by omega) (by omega) hu_not x
  have hC'_dirty : ∀ k < C'.size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue C' n x (n + k) = true ∧ circuitFun n C x = false := by
    intro k hk
    have hk_kl : k < kl.length := by
      change k < C'.gates.length at hk
      rw [← hC'_len]; exact hk
    have hprops := keepList_getElem_props keepB C.gates.length k hk_kl
    have hj_lt : kl[k] < C.gates.length := hprops.1
    have hj_not : ¬ WireBelowOutput n C (n + kl[k]) := (hkeepB_true kl[k]).mp hprops.2.1
    have hj_rank : rankOf keepB kl[k] = k := hprops.2.2
    have hex : ∃ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue C n x (n + kl[k]) = true ∧ circuitFun n C x = false := by
      by_contra hno
      apply hj_not
      intro x hx
      cases hcx : circuitFun n C x with
      | true => exact hcx
      | false => exact absurd ⟨x, hx, hcx⟩ hno
    obtain ⟨x, hx1, hx2⟩ := hex
    refine ⟨x, ?_, hx2⟩
    have hweq := hWireEq (n + kl[k]) (by omega) hj_not x
    have hwm : wmap (n + kl[k]) = n + k := by
      have hge : ¬ (n + kl[k] < n) := by omega
      simp only [wmap, hge, ↓reduceIte, Nat.add_sub_cancel_left, hj_rank]
    rw [← hwm, hweq]
    exact hx1
  set below := (Finset.range C.gates.length).filter (fun j => WireBelowOutput n C (n + j)) with hbelow_def
  have hOut_below : WireBelowOutput n C C.output := fun _ hx => hx
  have hOut_ge : n ≤ C.output := by
    by_contra hlt
    exact hNoIn C.output (by omega) hOut_below
  set jOut := C.output - n with hjOut_def
  have hjOut_eq : n + jOut = C.output := by omega
  have hjOut_lt : jOut < C.gates.length := by
    change C.output < n + C.gates.length at hOut
    omega
  have hjOut_mem : jOut ∈ below := by
    rw [hbelow_def, Finset.mem_filter, Finset.mem_range]
    exact ⟨hjOut_lt, by rw [hjOut_eq]; exact hOut_below⟩
  obtain ⟨S, D, hS_sub, hD_sub, hDisj, hCard, hS_top, hCov⟩ :=
    peel_below n C hAO hNoIn below hbelow_def below.card {jOut} ∅ (by simp)
      (Finset.singleton_subset_iff.mpr hjOut_mem) (Finset.empty_subset _)
      (Finset.disjoint_empty_right _) (by simp)
      (fun x hfx => ⟨jOut, Finset.mem_singleton_self jOut, by rw [hjOut_eq]; exact hfx⟩)
      (fun _ _ _ _ hd => absurd hd (Finset.notMem_empty _))
  let pairs : List (ℕ × ℕ) := S.toList.map (fun j => (wmap (opnd C j 0), wmap (opnd C j 1)))
  refine ⟨C', pairs, hC'_AO, hC'_dirty, ?_, ?_⟩
  · intro x
    constructor
    · intro hfx
      obtain ⟨j, hjS, hjx⟩ := hCov x hfx
      have htop := (isTopAndB_eq_true_iff n C j).mp (hS_top j hjS)
      obtain ⟨a, b, hab, ha_lt, hb_lt⟩ := gate_inputs_two n C hAO j htop.1
      have ha_not : ¬ WireBelowOutput n C a := htop.2.2.2 a (by simp [hab])
      have hb_not : ¬ WireBelowOutput n C b := htop.2.2.2 b (by simp [hab])
      have hop0 : opnd C j 0 = a := by simp [opnd, hab]
      have hop1 : opnd C j 1 = b := by simp [opnd, hab]
      rw [wireValue_and_pair n C hAO.2.1 j a b htop.1 htop.2.2.1 hab x, Bool.and_eq_true] at hjx
      refine ⟨(wmap a, wmap b), ?_, ?_, ?_⟩
      · simp only [pairs, List.mem_map, Finset.mem_toList]
        exact ⟨j, hjS, by rw [hop0, hop1]⟩
      · rw [hWireEq a (by omega) ha_not x]; exact hjx.1
      · rw [hWireEq b (by omega) hb_not x]; exact hjx.2
    · rintro ⟨p, hp, hp1, hp2⟩
      simp only [pairs, List.mem_map, Finset.mem_toList] at hp
      obtain ⟨j, hjS, rfl⟩ := hp
      have htop := (isTopAndB_eq_true_iff n C j).mp (hS_top j hjS)
      obtain ⟨a, b, hab, ha_lt, hb_lt⟩ := gate_inputs_two n C hAO j htop.1
      have ha_not : ¬ WireBelowOutput n C a := htop.2.2.2 a (by simp [hab])
      have hb_not : ¬ WireBelowOutput n C b := htop.2.2.2 b (by simp [hab])
      have hop0 : opnd C j 0 = a := by simp [opnd, hab]
      have hop1 : opnd C j 1 = b := by simp [opnd, hab]
      dsimp only at hp1 hp2
      rw [hop0] at hp1
      rw [hop1] at hp2
      rw [hWireEq a (by omega) ha_not x] at hp1
      rw [hWireEq b (by omega) hb_not x] at hp2
      apply htop.2.1 x
      change PEqualNP.BlindGate.wireValue C n x (n + j) = true
      rw [wireValue_and_pair n C hAO.2.1 j a b htop.1 htop.2.2.1 hab x, hp1, hp2]
      rfl
  · have hpair_len : pairs.length = S.card := by
      simp [pairs]
    have hSD_le : S.card + D.card ≤ below.card := by
      rw [← Finset.card_union_of_disjoint hDisj]
      exact Finset.card_le_card (Finset.union_subset hS_sub hD_sub)
    have hbelow_eq : below = (Finset.range C.gates.length).filter (fun j => keepB j = false) := by
      ext j
      simp [hbelow_def, hkeepB_false]
    have hsum_size : C'.size + below.card = C.size := by
      have h1 := rankOf_add_filter_card keepB C.gates.length
      rw [← hbelow_eq] at h1
      change C'.gates.length + below.card = C.gates.length
      rw [hC'_len]
      exact h1
    omega

end BlockSeparate

lemma blockSeparate :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output < x1 + x2.size → (∀ x5 < x1, ¬PEqualNP.CircuitMoves.WireBelowOutput x1 x2 x5) → (∀ x6 < x2.size, ∀ (x8 x9 : ℕ), x2.gates[x6]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x8, x9] : PEqualNP.CircuitLowerBounds.Gate } → (x1 ≤ x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x2 x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x2 x8) ∧ (x1 ≤ x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x2 x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x2 x9)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : List (ℕ × ℕ)), PEqualNP.TopForm.IsAO2 x1 x7 ∧ (∀ x9 < x7.size, ∃ (x11 : Fin x1 → Bool), PEqualNP.BlindGate.wireValue x7 x1 x11 (x1 + x9) = Bool.true ∧ PEqualNP.MetaComplexity.circuitFun x1 x2 x11 = Bool.false) ∧ (∀ (x9 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x9 = Bool.true ↔ ∃ x10 ∈ x8, PEqualNP.BlindGate.wireValue x7 x1 x9 x10.1 = Bool.true ∧ PEqualNP.BlindGate.wireValue x7 x1 x9 x10.2 = Bool.true) ∧ x7.size + (2 : ℕ) * x8.length ≤ x2.size + (1 : ℕ) :=
  PEqualNP.Outside.L_meta_2583.BlockSeparate.main_proof


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.CircuitMoves

lemma liftClosure (n : ℕ) (C C' : Circuit) (hC : IsAO2 n C)
    (hout : C.output < n + C.gates.length)
    (hsteps : Relation.ReflTransGen (Lift n) C C') :
    IsAO2 n C' ∧ C'.output < n + C'.gates.length ∧ C'.size = C.size ∧
      circuitFun n C' = circuitFun n C := by
  induction hsteps with
  | refl => exact ⟨hC, hout, rfl, rfl⟩
  | @tail D E hsteps hstep ih =>
    obtain ⟨hD, hoD, hsD, hfD⟩ := ih
    obtain ⟨hE, hoE, hsE, hfE⟩ := liftCorrect n D E hD hoD hstep
    exact ⟨hE, hoE, hsE.trans hsD, hfE.trans hfD⟩

lemma blocksAfterLifts (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (hout : C.output < n + C.size)
    (hinputs : ∀ w < n, ¬WireBelowOutput n C w) :
    ∃ (D : Circuit) (B : List (ℕ × ℕ)), IsAO2 n D ∧
      (∀ j < D.size, ∃ x, PEqualNP.BlindGate.wireValue D n x (n+j) = true ∧
        circuitFun n C x = false) ∧
      (∀ x, circuitFun n C x = true ↔ ∃ t ∈ B,
        PEqualNP.BlindGate.wireValue D n x t.1 = true ∧
        PEqualNP.BlindGate.wireValue D n x t.2 = true) ∧
      D.size + 2 * B.length ≤ C.size + 1 := by
  obtain ⟨E, hsteps, hfixed⟩ := liftNormalize n C hC hout
  obtain ⟨hE, hoE, hsE, hfE⟩ := liftClosure n C E hC hout hsteps
  have hinputsE : ∀ w < n, ¬WireBelowOutput n E w := by
    intro w hw hb
    apply hinputs w hw
    intro x hx
    have he : (E.wires (List.ofFn x)).getD w false =
        (C.wires (List.ofFn x)).getD w false := by
      have h1 := LiftCorrect.wiresFrom_input E.gates (List.ofFn x) w (by simpa using hw)
      have h2 := LiftCorrect.wiresFrom_input C.gates (List.ofFn x) w (by simpa using hw)
      exact h1.trans h2.symm
    have ht := hb x (he.trans hx)
    change circuitFun n E x = true at ht
    rwa [hfE] at ht
  obtain ⟨D, B, hD, hd, hb, hs⟩ := blockSeparate n E hE hoE hinputsE hfixed
  exact ⟨D, B, hD, by simpa only [hfE] using hd,
    by simpa only [hfE] using hb, by simpa only [hsE] using hs⟩

lemma incidenceInputsNotBelow {p l : ℕ} (I : Fin p → Fin l → Prop) [DecidableRel I]
    (C : Circuit)
    (correct : ∀ x, circuitFun (p+l) C x = decide (∃ a b, I a b ∧
      x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    ∀ w < p+l, ¬WireBelowOutput (p+l) C w := by
  intro w hw hb
  let x := fun i : Fin (p+l) => decide (i.val = w)
  have hx : (C.wires (List.ofFn x)).getD w false = true := by
    change (LiftCorrect.wiresFrom C.gates (List.ofFn x)).getD w false = true
    rw [LiftCorrect.wiresFrom_input _ _ _ (by simpa using hw),
      List.getD_eq_getElem _ _ (by simpa using hw), List.getElem_ofFn]
    simp [x]
  have ho : circuitFun (p+l) C x = true := hb x hx
  rw [correct x] at ho
  obtain ⟨a, b, _, ha, hb⟩ := of_decide_eq_true ho
  simp only [x, decide_eq_true_eq, Fin.val_castAdd, Fin.val_natAdd] at ha hb
  omega

lemma incidenceOutputValid {p l : ℕ} (I : Fin p → Fin l → Prop) [DecidableRel I]
    (C : Circuit) (nonempty : ∃ a b, I a b)
    (correct : ∀ x, circuitFun (p+l) C x = decide (∃ a b, I a b ∧
      x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    C.output < p+l+C.size := by
  let x := fun _ : Fin (p+l) => true
  have ho : circuitFun (p+l) C x = true := by
    rw [correct]
    apply decide_eq_true
    obtain ⟨a, b, hab⟩ := nonempty
    exact ⟨a, b, hab, rfl, rfl⟩
  by_contra h
  have hn : (C.wires (List.ofFn x)).length ≤ C.output := by
    change (LiftCorrect.wiresFrom C.gates (List.ofFn x)).length ≤ _
    rw [LiftCorrect.length_wiresFrom]
    simp only [List.length_ofFn]
    change ¬ C.output < p+l+C.gates.length at h
    omega
  change (C.wires (List.ofFn x)).getD C.output false = true at ho
  rw [List.getD_eq_default _ _ hn] at ho
  contradiction

lemma incidenceBlocks {p l : ℕ} (I : Fin p → Fin l → Prop) [DecidableRel I]
    (C : Circuit) (hC : IsAO2 (p+l) C) (nonempty : ∃ a b, I a b)
    (correct : ∀ x, circuitFun (p+l) C x = decide (∃ a b, I a b ∧
      x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    ∃ (D : Circuit) (B : List (ℕ × ℕ)), IsAO2 (p+l) D ∧
      (∀ j < D.size, ∃ x, PEqualNP.BlindGate.wireValue D (p+l) x (p+l+j) = true ∧
        ¬ ∃ a b, I a b ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true) ∧
      (∀ x, (∃ a b, I a b ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true) ↔
        ∃ t ∈ B, PEqualNP.BlindGate.wireValue D (p+l) x t.1 = true ∧
          PEqualNP.BlindGate.wireValue D (p+l) x t.2 = true) ∧
      D.size + 2 * B.length ≤ C.size + 1 := by
  obtain ⟨D, B, hD, hd, hb, hs⟩ := blocksAfterLifts (p+l) C hC
    (incidenceOutputValid I C nonempty correct) (incidenceInputsNotBelow I C correct)
  refine ⟨D, B, hD, ?_, ?_, hs⟩
  · intro j hj
    obtain ⟨x, hx, hf⟩ := hd j hj
    exact ⟨x, hx, of_decide_eq_false (by simpa only [correct] using hf)⟩
  · intro x
    simpa only [correct, decide_eq_true_eq] using hb x

end PEqualNP.Outside.L_meta_2583


namespace PEqualNP.Outside.L_meta_2583_aux.EdgeInvisible

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CircuitMoves

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_split (gs : List Gate) (w : List Bool) (j : ℕ) :
    W gs w = W (gs.drop j) (W (gs.take j) w) := by
  rw [← W_append, List.take_append_drop]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem W_gate_pre (gs pre post : List Gate) (g : Gate) (w : List Bool)
    (h : gs = pre ++ g :: post) :
    (W gs w).getD (w.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (W pre w).getD i false) := by
  subst h
  rw [W_append, W_cons, W_prefix _ _ _ (by rw [step_len, W_length]; omega)]
  exact step_last _ _ _ (by rw [W_length])

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

theorem getElem?_gateAt {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g ∧ j < C.gates.length := by
  have hj : j < C.gates.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨?_, hj⟩
  rw [gateAt_eq hj]
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

theorem val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := W_prefix _ _ _ (by omega)

theorem val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := W_ge _ _ _ (by omega)

theorem val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact W_gate C.gates x j hj

theorem val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

theorem val_ofFn_lt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    val C (List.ofFn x) u = x ⟨u, hu⟩ := val_ofFn C x ⟨u, hu⟩

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

theorem opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

theorem val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

theorem isAO2_rb {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) {i : ℕ} (hi : i ∈ (gateAt C j).inputs) : i < n + j :=
  h.2.1 j hj i hi

theorem mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : val C (List.ofFn x) w = x ⟨w, hw⟩ := val_ofFn C x ⟨w, hw⟩
      have e2 : val C (List.ofFn y) w = y ⟨w, hw⟩ := val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then val C (List.ofFn x) i else false) = true →
              (if i < n + k then val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]
            exact ih i hi
          · rw [if_neg hi, if_neg hi]
            exact id
        exact opMono_imp (gateAt C k).op (hAO _ (gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then val C (List.ofFn x) i else false)
          (fun i => if i < n + k then val C (List.ofFn y) i else false) h hv

theorem and_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    val C x (n + j) = (val C x ((gateAt C j).inputs.getD 0 0) &&
      val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

theorem or_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    val C x (n + j) = (val C x ((gateAt C j).inputs.getD 0 0) ||
      val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

theorem orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega

theorem orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.CleanedNonEdge.orStep n (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
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
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []) := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
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
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
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
    · have e0 : (PEqualNP.CleanedNonEdge.orStep n
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ k < C.gates.length ∧
      (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ PEqualNP.CleanedNonEdge.OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold PEqualNP.CleanedNonEdge.OrReaches PEqualNP.CleanedNonEdge.orSets gateAt
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

theorem orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) j :=
  (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩

theorem orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C i g) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g :=
  (orReaches_iff n C j g).mpr ⟨hj, Or.inr ⟨hop, i, hi, hlt, h⟩⟩

theorem orReaches_bound (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g → n + g ≤ w ∧ w < n + C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp hr
    rcases h3 with h3 | ⟨_, i, _, hlt, hri⟩
    · omega
    · have := ih i hlt hri
      omega

theorem reach_up (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (j : ℕ)
    (hv : val C x (n + j) = true) :
    ∀ b : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C b j → val C x b = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hr
    have hnb : n ≤ b := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k j).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]
      exact hv
    · exact (val_or hx hk hop).mpr ⟨i, hi, hlt, ih i hlt hri⟩

def erase_rg (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

theorem erase_redirect_lt (n m p i : ℕ) (h : i < n + m) : eraseRedirect n m p i = i := by
  unfold eraseRedirect
  rw [if_neg (by omega), if_neg (by omega)]

theorem erase_redirect_self (n m p : ℕ) : eraseRedirect n m p (n + m) = p := by
  unfold eraseRedirect
  rw [if_pos rfl]

theorem erase_redirect_gt (n m p i : ℕ) (h : n + m < i) : eraseRedirect n m p i = i - 1 := by
  unfold eraseRedirect
  rw [if_neg (by omega), if_pos h]

theorem erase_redirect_succ (n m p k : ℕ) (h : n + m ≤ k) : eraseRedirect n m p (k + 1) = k := by
  rw [erase_redirect_gt n m p (k + 1) (by omega), Nat.add_sub_cancel]

theorem erase_snoc_eq (a : List Bool) (v : Bool) (i : ℕ) (h : i = a.length) :
    (a ++ [v]).getD i false = v := by
  subst h
  exact getD_app_len a v

theorem erase_snoc_gt (a : List Bool) (v : Bool) (i : ℕ) (h : a.length < i) :
    (a ++ [v]).getD i false = false :=
  getD_ge _ _ (by rw [List.length_append, List.length_singleton]; omega)

theorem erase_step_rel (rel : Bool → Bool → Prop) (h00 : rel false false) (n m p : ℕ)
    (hp : p < n + m) (a b : List Bool) (va vb : Bool) (hl : a.length = b.length + 1)
    (hn : n + m < a.length)
    (h : ∀ i, rel (a.getD i false) (b.getD (eraseRedirect n m p i) false)) (hv : rel va vb) :
    ∀ i, rel ((a ++ [va]).getD i false) ((b ++ [vb]).getD (eraseRedirect n m p i) false) := by
  intro i
  by_cases hi : i < a.length
  · have hri : eraseRedirect n m p i < b.length := by
      unfold eraseRedirect
      split_ifs <;> omega
    rw [getD_app_lt a [va] i hi, getD_app_lt b [vb] _ hri]
    exact h i
  · rw [erase_redirect_gt n m p i (by omega)]
    by_cases hi2 : i = a.length
    · rw [erase_snoc_eq a va i hi2, erase_snoc_eq b vb (i - 1) (by omega)]
      exact hv
    · rw [erase_snoc_gt a va i (by omega), erase_snoc_gt b vb (i - 1) (by omega)]
      exact h00

theorem erase_W_rel (Q : GateOp → Prop) (rel : Bool → Bool → Prop) (h00 : rel false false)
    (n m p : ℕ) (hp : p < n + m)
    (hop : ∀ (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool), Q op →
      (∀ i, rel (f i) (f' (eraseRedirect n m p i))) →
      rel (op.eval (l.map f)) (op.eval ((l.map (eraseRedirect n m p)).map f')))
    (gs : List Gate) : ∀ (a b : List Bool), (∀ g ∈ gs, Q g.op) →
      a.length = b.length + 1 → n + m < a.length →
      (∀ i, rel (a.getD i false) (b.getD (eraseRedirect n m p i) false)) →
      ∀ i, rel ((W gs a).getD i false)
        ((W (gs.map (erase_rg (eraseRedirect n m p))) b).getD (eraseRedirect n m p i) false) := by
  induction gs with
  | nil => intro a b _ _ _ h i; exact h i
  | cons g gs ih =>
    intro a b hg hl hn h i
    rw [List.map_cons, W_cons, W_cons]
    refine ih (step a g) (step b (erase_rg (eraseRedirect n m p) g)) ?_ ?_ ?_ ?_ i
    · intro g' hg'
      exact hg g' (List.mem_cons_of_mem _ hg')
    · rw [step_len, step_len, hl]
    · rw [step_len]
      omega
    · exact erase_step_rel rel h00 n m p hp a b
        (g.op.eval (g.inputs.map fun i => a.getD i false))
        (g.op.eval ((g.inputs.map (eraseRedirect n m p)).map fun i => b.getD i false))
        hl hn h
        (hop g.op g.inputs (fun i => a.getD i false) (fun i => b.getD i false)
          (hg g (by simp)) h)

theorem erase_sem (Q : GateOp → Prop) (rel : Bool → Bool → Prop) (hrefl : ∀ b, rel b b)
    (n m p : ℕ) (hp : p < n + m)
    (hop : ∀ (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool), Q op →
      (∀ i, rel (f i) (f' (eraseRedirect n m p i))) →
      rel (op.eval (l.map f)) (op.eval ((l.map (eraseRedirect n m p)).map f')))
    (pre post : List Gate) (gm : Gate) (x : List Bool) (hx : x.length = n)
    (hpre : pre.length = m)
    (hpost : ∀ g ∈ post, Q g.op)
    (hbase : rel (gm.op.eval (gm.inputs.map fun i => (W pre x).getD i false))
      ((W pre x).getD p false)) :
    ∀ i, rel ((W (pre ++ gm :: post) x).getD i false)
      ((W (pre ++ post.map (erase_rg (eraseRedirect n m p))) x).getD
        (eraseRedirect n m p i) false) := by
  have hA : (W pre x).length = n + m := by rw [W_length, hx, hpre]
  rw [W_append, W_append, W_cons]
  refine erase_W_rel Q rel (hrefl false) n m p hp hop post (step (W pre x) gm) (W pre x)
    hpost ?_ ?_ ?_
  · exact step_len _ _
  · rw [step_len, hA]
    omega
  · intro i
    show rel ((W pre x ++ [gm.op.eval (gm.inputs.map fun i => (W pre x).getD i false)]).getD i
      false) ((W pre x).getD (eraseRedirect n m p i) false)
    by_cases hi : i < n + m
    · rw [erase_redirect_lt n m p i hi, getD_app_lt (W pre x) _ i (by omega)]
      exact hrefl _
    · by_cases hi2 : i = n + m
      · rw [hi2, erase_redirect_self n m p, erase_snoc_eq (W pre x) _ (n + m) hA.symm]
        exact hbase
      · rw [erase_redirect_gt n m p i (by omega), erase_snoc_gt (W pre x) _ i (by omega),
          getD_ge (W pre x) (i - 1) (by omega)]
        exact hrefl false

theorem erase_eq (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    eraseGate n C m p = Circuit.mk
      (C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p)))
      (eraseRedirect n m p C.output) := if_pos hm

theorem erase_gates (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates
      = C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p)) :=
  congrArg Circuit.gates (erase_eq n C m p hm)

theorem erase_output (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).output = eraseRedirect n m p C.output :=
  congrArg Circuit.output (erase_eq n C m p hm)

theorem erase_length (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates.length + 1 = C.gates.length := by
  rw [erase_gates n C m p hm, List.length_append, List.length_take, List.length_map,
    List.length_drop]
  omega

theorem erase_size (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).size + 1 = C.size := by
  show (eraseGate n C m p).gates.length + 1 = C.gates.length
  exact erase_length n C m p hm

theorem erase_getD (l : List Gate) (f : Gate → Gate) (d : Gate) (m j : ℕ) (hm : m < l.length)
    (hj : j + 1 < l.length) :
    (l.take m ++ (l.drop (m + 1)).map f).getD j d
      = if j < m then l.getD j d else f (l.getD (j + 1) d) := by
  have hlt : (l.take m).length = m := by
    rw [List.length_take]
    omega
  by_cases h : j < m
  · rw [if_pos h, List.getD_append _ _ _ _ (by omega)]
    rw [List.getD_eq_getElem (l.take m) d (by omega), List.getD_eq_getElem l d (by omega),
      List.getElem_take]
  · rw [if_neg h, List.getD_append_right _ _ _ _ (by omega), hlt]
    have e : m + 1 + (j - m) = j + 1 := by omega
    rw [List.getD_eq_getElem (List.map f (l.drop (m + 1))) d
        (by rw [List.length_map, List.length_drop]; omega),
      List.getD_eq_getElem l d hj, List.getElem_map, List.getElem_drop]
    simp only [e]

theorem erase_gateAt (n : ℕ) (C : Circuit) (m p j : ℕ) (hm : m < C.gates.length)
    (hj : j + 1 < C.gates.length) :
    gateAt (eraseGate n C m p) j
      = if j < m then gateAt C j else erase_rg (eraseRedirect n m p) (gateAt C (j + 1)) := by
  have h0 : gateAt (eraseGate n C m p) j
      = (C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p))).getD j
        (Gate.mk GateOp.or []) :=
    congrArg (fun gs : List Gate => gs.getD j (Gate.mk GateOp.or [])) (erase_gates n C m p hm)
  rw [h0]
  exact erase_getD C.gates (erase_rg (eraseRedirect n m p)) (Gate.mk GateOp.or []) m j hm hj

theorem erase_gateAt_ge (n : ℕ) (C : Circuit) (m p j : ℕ) (hm : m < C.gates.length)
    (hj : m ≤ j) (hj1 : j + 1 < C.gates.length) :
    gateAt (eraseGate n C m p) j = erase_rg (eraseRedirect n m p) (gateAt C (j + 1)) := by
  rw [erase_gateAt n C m p j hm hj1, if_neg (Nat.not_lt.mpr hj)]

theorem erase_andOrOnly (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (hA : PEqualNP.EdgeOwnership.AndOrOnly C) :
    PEqualNP.EdgeOwnership.AndOrOnly (eraseGate n C m p) := by
  intro g hg
  rw [erase_gates n C m p hm] at hg
  rcases List.mem_append.1 hg with h | h
  · exact hA g (List.mem_of_mem_take h)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
    exact hA g0 (List.mem_of_mem_drop hg0)

theorem erase_readsBack (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (hp : p < n + m) (hR : ReadsBack n C) : ReadsBack n (eraseGate n C m p) := by
  have hElen := erase_length n C m p hm
  intro j hj i hi
  rw [erase_gateAt n C m p j hm (by omega)] at hi
  by_cases hjm : j < m
  · rw [if_pos hjm] at hi
    exact hR j (by omega) i hi
  · rw [if_neg hjm] at hi
    have hi' : i ∈ (gateAt C (j + 1)).inputs.map (eraseRedirect n m p) := hi
    obtain ⟨i0, hi0, rfl⟩ := List.mem_map.1 hi'
    have h2 := hR (j + 1) (by omega) i0 hi0
    unfold eraseRedirect
    split_ifs <;> omega

theorem erase_val_lt {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m < C.gates.length)
    {x : List Bool} (hx : x.length = n) {i : ℕ} (hi : i < n + m) :
    val (eraseGate n C m p) x i = val C x i := by
  have hpre : (C.gates.take m).length = m := by
    rw [List.length_take]
    omega
  have hA : (W (C.gates.take m) x).length = n + m := by rw [W_length, hx, hpre]
  have e1 : val (eraseGate n C m p) x i
      = (W (C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p))) x).getD
        i false :=
    congrArg (fun gs : List Gate => (W gs x).getD i false) (erase_gates n C m p hm)
  have e2 : val C x i = (W (C.gates.take m ++ C.gates.drop m) x).getD i false :=
    congrArg (fun gs : List Gate => (W gs x).getD i false) (List.take_append_drop m C.gates).symm
  rw [e1, e2, W_append, W_append,
    W_prefix ((C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p)))
      (W (C.gates.take m) x) i (by omega),
    W_prefix (C.gates.drop m) (W (C.gates.take m) x) i (by omega)]

theorem erase_val_rel (Q : GateOp → Prop) (rel : Bool → Bool → Prop) (hrefl : ∀ b, rel b b)
    {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m < C.gates.length) (hp : p < n + m)
    (hop : ∀ (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool), Q op →
      (∀ i, rel (f i) (f' (eraseRedirect n m p i))) →
      rel (op.eval (l.map f)) (op.eval ((l.map (eraseRedirect n m p)).map f')))
    (hQ : ∀ g ∈ C.gates.drop (m + 1), Q g.op)
    {x : List Bool} (hx : x.length = n) (hv : rel (val C x (n + m)) (val C x p)) :
    ∀ i, rel (val C x i) (val (eraseGate n C m p) x (eraseRedirect n m p i)) := by
  have hsplit : C.gates.take m ++ gateAt C m :: C.gates.drop (m + 1) = C.gates := by
    rw [gateAt_eq hm, ← List.drop_eq_getElem_cons hm, List.take_append_drop]
  have hpre : (C.gates.take m).length = m := by
    rw [List.length_take]
    omega
  have hA : (W (C.gates.take m) x).length = n + m := by rw [W_length, hx, hpre]
  have e1 : val C x (n + m) = (gateAt C m).op.eval
      ((gateAt C m).inputs.map fun i => (W (C.gates.take m) x).getD i false) := by
    have h1 := W_gate_pre C.gates (C.gates.take m) (C.gates.drop (m + 1)) (gateAt C m) x
      hsplit.symm
    rw [hx, hpre] at h1
    exact h1
  have e2 : val C x p = (W (C.gates.take m) x).getD p false := by
    show (W C.gates x).getD p false = _
    rw [W_split C.gates x m]
    exact W_prefix _ _ _ (by omega)
  rw [e1, e2] at hv
  have key := erase_sem Q rel hrefl n m p hp hop (C.gates.take m) (C.gates.drop (m + 1))
    (gateAt C m) x hx hpre hQ hv
  have hW : ∀ i, val C x i
      = (W (C.gates.take m ++ gateAt C m :: C.gates.drop (m + 1)) x).getD i false :=
    fun i => congrArg (fun gs : List Gate => (W gs x).getD i false) hsplit.symm
  have hWD : ∀ i, val (eraseGate n C m p) x i
      = (W (C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p))) x).getD
        i false :=
    fun i => congrArg (fun gs : List Gate => (W gs x).getD i false) (erase_gates n C m p hm)
  intro i
  rw [hW i, hWD (eraseRedirect n m p i)]
  exact key i

theorem cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.EdgeOwnership.coneStep]
    omega

theorem cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
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
      have e2 : (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
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
    · have e0 : (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    PEqualNP.EdgeOwnership.InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧
      n + k ∈ (gateAt C j).inputs ∧ (i = k ∨ PEqualNP.EdgeOwnership.InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold PEqualNP.EdgeOwnership.InCone PEqualNP.EdgeOwnership.cones gateAt
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

theorem inCone_of_read (n : ℕ) (C : Circuit) (k j : ℕ) (hj : j < C.gates.length) (hk : k < j)
    (hin : n + k ∈ (gateAt C j).inputs) : PEqualNP.EdgeOwnership.InCone n C k j :=
  (inCone_iff n C k j).mpr ⟨hj, k, hk, hin, Or.inl rfl⟩

theorem inCone_trans (n : ℕ) (C : Circuit) (i k : ℕ) (hik : PEqualNP.EdgeOwnership.InCone n C i k) :
    ∀ j, PEqualNP.EdgeOwnership.InCone n C k j → PEqualNP.EdgeOwnership.InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k', hk', hin, h3⟩ := h
    rw [inCone_iff]
    refine ⟨h0, k', hk', hin, Or.inr ?_⟩
    rcases h3 with h3 | h3
    · rw [← h3]; exact hik
    · exact ih k' hk' h3

theorem p47_mem2 (l : List ℕ) (h : l.length = 2) (t : ℕ) (ht : t < 2) : l.getD t 0 ∈ l := by
  rw [List.getD_eq_getElem l 0 (by omega : t < l.length)]
  apply List.getElem_mem

theorem p47_map_getD (l : List ℕ) (r : ℕ → ℕ) (t : ℕ) (ht : t < l.length) :
    (l.map r).getD t 0 = r (l.getD t 0) := by
  have h2 : t < (l.map r).length := by rw [List.length_map]; exact ht
  rw [List.getD_eq_getElem (l.map r) 0 h2, List.getD_eq_getElem l 0 ht, List.getElem_map]

theorem p47_pair_val {n : ℕ} (C : Circuit) (u z : Fin n) (w : ℕ) (hw : w < n) :
    val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) w = decide (w = u.val ∨ w = z.val) := by
  rw [val_ofFn_lt C _ w hw]
  simp [PEqualNP.EdgeOwnership.pairInput, Fin.ext_iff]

theorem p47_unit_val {n : ℕ} (C : Circuit) (u : Fin n) (w : ℕ) (hw : w < n) :
    val C (List.ofFn (PEqualNP.SplitCount.unitInput u)) w = decide (w = u.val) := by
  rw [val_ofFn_lt C _ w hw]
  simp [PEqualNP.SplitCount.unitInput, Fin.ext_iff]

theorem p47_isAO2_erase (n : ℕ) (C : Circuit) (g v : ℕ) (hg : g < C.gates.length) (hv : v < n + g)
    (hAO : PEqualNP.TopForm.IsAO2 n C) : PEqualNP.TopForm.IsAO2 n (eraseGate n C g v) := by
  refine ⟨erase_andOrOnly n C g v hg hAO.1, erase_readsBack n C g v hg hv hAO.2.1, ?_⟩
  intro gt hgt
  rw [erase_gates n C g v hg] at hgt
  rcases List.mem_append.1 hgt with h | h
  · exact hAO.2.2 _ (List.mem_of_mem_take h)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
    show (g0.inputs.map _).length = 2
    rw [List.length_map]
    exact hAO.2.2 g0 (List.mem_of_mem_drop hg0)

theorem p47_rec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (u z : Fin n)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hLF : PEqualNP.Core.IsLiftFixedPoint G C)
    (hcone : ∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k)
    (hbelow : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g →
      PEqualNP.TopForm.BelowF G C k) :
    ∀ w : ℕ, (¬ ∀ x : Fin n → Bool, val C (List.ofFn x) w = true → graphFun G ∅ x = true) →
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) w = true →
      val C (List.ofFn (PEqualNP.SplitCount.unitInput u)) w = true ∨
      val C (List.ofFn (PEqualNP.SplitCount.unitInput z)) w = true ∨
      PEqualNP.CleanedNonEdge.OrReaches n C w g := by
  unfold PEqualNP.Core.IsLiftFixedPoint PEqualNP.Core.LiftApplies PEqualNP.Core.LiftAt
    PEqualNP.Core.IsImpWire at hLF
  unfold PEqualNP.TopForm.BelowF at hbelow
  have hx : ∀ y : Fin n → Bool, (List.ofFn y).length = n := fun y => by simp
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hnb hv
    by_cases hwn : w < n
    · rw [p47_pair_val C u z w hwn, decide_eq_true_eq] at hv
      rcases hv with h | h
      · left
        rw [p47_unit_val C u w hwn, decide_eq_true_eq]
        exact h
      · right; left
        rw [p47_unit_val C z w hwn, decide_eq_true_eq]
        exact h
    · by_cases hwl : w < n + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
        rcases hAO.1 _ (gateAt_mem hj) with hop | hop
        · by_cases hjg : j = g
          · subst hjg
            exact Or.inr (Or.inr (orReaches_self n C j hj))
          · exact absurd (fun x hx' => hbelow j hj hop hjg x hx') hnb
        · have key : ∀ t : ℕ, t < 2 →
              val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z))
                ((gateAt C j).inputs.getD t 0) = true →
              val C (List.ofFn (PEqualNP.SplitCount.unitInput u)) (n + j) = true ∨
              val C (List.ofFn (PEqualNP.SplitCount.unitInput z)) (n + j) = true ∨
              PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g := by
            intro t ht hvt
            have hmem := p47_mem2 _ hlen t ht
            have hlt := isAO2_rb hAO hj hmem
            have hnbt : ¬ ∀ x : Fin n → Bool, val C (List.ofFn x) ((gateAt C j).inputs.getD t 0) = true →
                graphFun G ∅ x = true := by
              intro hb
              apply hLF
              exact ⟨j, hj, ⟨t, ht⟩, hcone j hj, hop, fun hb2 => hnb (fun x hx' => hb2 x hx'), hb,
                PEqualNP.EdgeOwnership.pairInput u z, hvt⟩
            have hup : ∀ y : Fin n → Bool, val C (List.ofFn y) ((gateAt C j).inputs.getD t 0) = true →
                val C (List.ofFn y) (n + j) = true := by
              intro y hy
              rw [or_val n C hAO _ (hx y) j hj hop]
              rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
              · rw [hy, Bool.true_or]
              · rw [hy, Bool.or_true]
            rcases ih _ hlt hnbt hvt with h | h | h
            · exact Or.inl (hup _ h)
            · exact Or.inr (Or.inl (hup _ h))
            · exact Or.inr (Or.inr (orReaches_step n C j _ g hj hop hmem hlt h))
          rw [or_val n C hAO _ (hx _) j hj hop, Bool.or_eq_true] at hv
          rcases hv with h | h
          · exact key 0 (by omega) h
          · exact key 1 (by omega) h
      · rw [val_ge (C := C) (hx _) (by omega)] at hv
        exact absurd hv (by simp)

theorem p47_both {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g j : ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hbelow : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g →
      PEqualNP.TopForm.BelowF G C k)
    (hgnb : ¬ PEqualNP.TopForm.BelowF G C g)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (h0 : PEqualNP.CleanedNonEdge.OrReaches n C ((gateAt C j).inputs.getD 0 0) g)
    (h1 : PEqualNP.CleanedNonEdge.OrReaches n C ((gateAt C j).inputs.getD 1 0) g) : False := by
  unfold PEqualNP.TopForm.BelowF at hbelow hgnb
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  have hjg : j ≠ g := by
    intro hjg
    subst hjg
    have b1 := (orReaches_bound n C j _ h0).1
    have b2 := isAO2_rb hAO hj (p47_mem2 _ hlen 0 (by omega))
    omega
  apply hgnb
  intro x hx
  apply hbelow j hj hop hjg x
  show val C (List.ofFn x) (n + j) = true
  have hx' : val C (List.ofFn x) (n + g) = true := hx
  rw [and_val n C hAO _ (by simp) j hj hop, reach_up n C _ (by simp) g hx' _ h0,
    reach_up n C _ (by simp) g hx' _ h1]
  rfl

def p40cf (C : Circuit) (g : ℕ) : Circuit := ⟨C.gates.set g ⟨GateOp.or, []⟩, C.output⟩

theorem p40_len (C : Circuit) (g : ℕ) : (p40cf C g).gates.length = C.gates.length := by
  simp [p40cf]

theorem p40_gateAt (C : Circuit) (g j : ℕ) (h : g ≠ j) : gateAt (p40cf C g) j = gateAt C j := by
  simp [p40cf, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set, h]

theorem p40_gateAt_self (C : Circuit) (g : ℕ) (hg : g < C.gates.length) :
    gateAt (p40cf C g) g = ⟨GateOp.or, []⟩ := by
  simp [p40cf, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set, hg]

theorem p40_aoo (C : Circuit) (g : ℕ) (hA : PEqualNP.EdgeOwnership.AndOrOnly C) :
    PEqualNP.EdgeOwnership.AndOrOnly (p40cf C g) := by
  intro gt hgt
  rcases List.mem_or_eq_of_mem_set hgt with h | h
  · exact hA gt h
  · rw [h]; exact Or.inr rfl

theorem p40_self {n : ℕ} (C : Circuit) (g : ℕ) (hg : g < C.gates.length) (x : List Bool)
    (hx : x.length = n) : val (p40cf C g) x (n + g) = false := by
  rw [val_gate (C := p40cf C g) hx (by rw [p40_len]; exact hg), p40_gateAt_self C g hg]
  rfl

theorem p40_and {n : ℕ} (C : Circuit) (g : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length) (hjg : j ≠ g)
    (hop : (gateAt C j).op = GateOp.and) :
    val (p40cf C g) x (n + j) = (val (p40cf C g) x ((gateAt C j).inputs.getD 0 0) &&
      val (p40cf C g) x ((gateAt C j).inputs.getD 1 0)) := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hAO.2.1 j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate (C := p40cf C g) hx (by rw [p40_len]; exact hj), p40_gateAt C g j (Ne.symm hjg), hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

theorem p40_or {n : ℕ} (C : Circuit) (g : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length) (hjg : j ≠ g)
    (hop : (gateAt C j).op = GateOp.or) :
    val (p40cf C g) x (n + j) = (val (p40cf C g) x ((gateAt C j).inputs.getD 0 0) ||
      val (p40cf C g) x ((gateAt C j).inputs.getD 1 0)) := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hAO.2.1 j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate (C := p40cf C g) hx (by rw [p40_len]; exact hj), p40_gateAt C g j (Ne.symm hjg), hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

theorem p40_le {n : ℕ} (C : Circuit) (g : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hg : g < C.gates.length) (x : List Bool) (hx : x.length = n) :
    ∀ i, val (p40cf C g) x i = true → val C x i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h
    by_cases h1 : i < n
    · rw [val_input (C := p40cf C g) hx h1] at h
      rw [val_input (C := C) hx h1]
      exact h
    by_cases h2 : i < n + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      have hj : j < C.gates.length := by omega
      by_cases hjg : j = g
      · subst hjg
        rw [p40_self C j hg x hx] at h
        exact absurd h (by simp)
      have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
      have l0 := isAO2_rb hAO hj (p47_mem2 _ hlen 0 (by omega))
      have l1 := isAO2_rb hAO hj (p47_mem2 _ hlen 1 (by omega))
      rcases hAO.1 _ (gateAt_mem hj) with hop | hop
      · rw [p40_and C g hAO x hx j hj hjg hop, Bool.and_eq_true] at h
        rw [and_val n C hAO x hx j hj hop, Bool.and_eq_true]
        exact ⟨ih _ l0 h.1, ih _ l1 h.2⟩
      · rw [p40_or C g hAO x hx j hj hjg hop, Bool.or_eq_true] at h
        rw [or_val n C hAO x hx j hj hop, Bool.or_eq_true]
        rcases h with h | h
        · exact Or.inl (ih _ l0 h)
        · exact Or.inr (ih _ l1 h)
    · rw [val_ge (C := p40cf C g) hx (by rw [p40_len]; omega)] at h
      exact absurd h (by simp)

theorem p40_eq_all {n : ℕ} (C : Circuit) (g : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hg : g < C.gates.length) (x : List Bool) (hx : x.length = n)
    (hge : val C x (n + g) = false) :
    ∀ i, val (p40cf C g) x i = val C x i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h1 : i < n
    · rw [val_input (C := p40cf C g) hx h1, val_input (C := C) hx h1]
    by_cases h2 : i < n + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      have hj : j < C.gates.length := by omega
      by_cases hjg : j = g
      · subst hjg
        rw [p40_self C j hg x hx, hge]
      have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
      have l0 := isAO2_rb hAO hj (p47_mem2 _ hlen 0 (by omega))
      have l1 := isAO2_rb hAO hj (p47_mem2 _ hlen 1 (by omega))
      rcases hAO.1 _ (gateAt_mem hj) with hop | hop
      · rw [p40_and C g hAO x hx j hj hjg hop, and_val n C hAO x hx j hj hop, ih _ l0, ih _ l1]
      · rw [p40_or C g hAO x hx j hj hjg hop, or_val n C hAO x hx j hj hop, ih _ l0, ih _ l1]
    · rw [val_ge (C := p40cf C g) hx (by rw [p40_len]; omega), val_ge (C := C) hx (by omega)]

theorem p40_other {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (u z : Fin n)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hLF : PEqualNP.Core.IsLiftFixedPoint G C)
    (hcone : ∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k)
    (hbelow : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g →
      PEqualNP.TopForm.BelowF G C k)
    (hadj : G.Adj u z)
    (hge : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g) = true)
    (d : ℕ) (hdnb : ¬ ∀ x : Fin n → Bool, val C (List.ofFn x) d = true → graphFun G ∅ x = true)
    (hdg : ¬ PEqualNP.CleanedNonEdge.OrReaches n C d g)
    (hk : ∀ a b : Fin n, G.Adj a b → val C (List.ofFn (PEqualNP.SplitCount.unitInput b)) d = true →
      PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput a b) = false) :
    val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) d = false := by
  have hsw : PEqualNP.EdgeOwnership.pairInput z u = PEqualNP.EdgeOwnership.pairInput u z := by
    funext w
    simp [PEqualNP.EdgeOwnership.pairInput, or_comm]
  cases hd : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) d
  · rfl
  exfalso
  rcases p47_rec G C g u z hAO hLF hcone hbelow d hdnb hd with h | h | h
  · have h2 := hk z u hadj.symm h
    rw [hsw] at h2
    have h3 : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g) = false := h2
    rw [hge] at h3
    exact absurd h3 (by simp)
  · have h2 := hk u z hadj h
    have h3 : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g) = false := h2
    rw [hge] at h3
    exact absurd h3 (by simp)
  · exact hdg h

theorem p40_eq_reach {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (u z : Fin n)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hLF : PEqualNP.Core.IsLiftFixedPoint G C)
    (hcone : ∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k)
    (hbelow : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g →
      PEqualNP.TopForm.BelowF G C k)
    (hg : g < C.gates.length)
    (hNB : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ t ∈ (gateAt C k).inputs,
      ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → graphFun G ∅ x = true))
    (hgnb : ¬ PEqualNP.TopForm.BelowF G C g)
    (hkey : ∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u z : Fin n, G.Adj u z → (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 0) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 1) (PEqualNP.SplitCount.unitInput z) = true) ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 1) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 0) (PEqualNP.SplitCount.unitInput z) = true) → PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput u z) = false)
    (hadj : G.Adj u z)
    (hge : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g) = true) :
    ∀ i, ¬ PEqualNP.CleanedNonEdge.OrReaches n C i g →
      val (p40cf C g) (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) i =
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) i := by
  have hx : (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)).length = n := by simp
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h1 : i < n
    · rw [val_input (C := p40cf C g) hx h1, val_input (C := C) hx h1]
    by_cases h2 : i < n + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      have hj : j < C.gates.length := by omega
      by_cases hjg : j = g
      · subst hjg
        exact absurd (orReaches_self n C j hj) hi
      have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
      have m0 := p47_mem2 _ hlen 0 (by omega)
      have m1 := p47_mem2 _ hlen 1 (by omega)
      have l0 := isAO2_rb hAO hj m0
      have l1 := isAO2_rb hAO hj m1
      rcases hAO.1 _ (gateAt_mem hj) with hop | hop
      · rw [p40_and C g hAO _ hx j hj hjg hop, and_val n C hAO _ hx j hj hop]
        by_cases r0 : PEqualNP.CleanedNonEdge.OrReaches n C ((gateAt C j).inputs.getD 0 0) g
        · by_cases r1 : PEqualNP.CleanedNonEdge.OrReaches n C ((gateAt C j).inputs.getD 1 0) g
          · exact (p47_both G C g j hAO hbelow hgnb hj hop r0 r1).elim
          · have hf := p40_other G C g u z hAO hLF hcone hbelow hadj hge
              ((gateAt C j).inputs.getD 1 0) (hNB j hj hop _ m1) r1
              (fun a b hab hb => hkey j hj hop a b hab (Or.inl ⟨r0, hb⟩))
            rw [ih _ l1 r1, hf]
            simp
        · by_cases r1 : PEqualNP.CleanedNonEdge.OrReaches n C ((gateAt C j).inputs.getD 1 0) g
          · have hf := p40_other G C g u z hAO hLF hcone hbelow hadj hge
              ((gateAt C j).inputs.getD 0 0) (hNB j hj hop _ m0) r0
              (fun a b hab hb => hkey j hj hop a b hab (Or.inr ⟨r1, hb⟩))
            rw [ih _ l0 r0, hf]
            simp
          · rw [ih _ l0 r0, ih _ l1 r1]
      · rw [p40_or C g hAO _ hx j hj hjg hop, or_val n C hAO _ hx j hj hop]
        have r0 : ¬ PEqualNP.CleanedNonEdge.OrReaches n C ((gateAt C j).inputs.getD 0 0) g :=
          fun h => hi (orReaches_step n C j _ g hj hop m0 l0 h)
        have r1 : ¬ PEqualNP.CleanedNonEdge.OrReaches n C ((gateAt C j).inputs.getD 1 0) g :=
          fun h => hi (orReaches_step n C j _ g hj hop m1 l1 h)
        rw [ih _ l0 r0, ih _ l1 r1]
    · rw [val_ge (C := p40cf C g) hx (by rw [p40_len]; omega), val_ge (C := C) hx (by omega)]

theorem p40_reader (n : ℕ) (C : Circuit) (h : ℕ) :
    ∀ o, PEqualNP.EdgeOwnership.InCone n C h o → ∃ k, n + h ∈ (gateAt C k).inputs ∧
      k < C.gates.length ∧ (k = o ∨ PEqualNP.EdgeOwnership.InCone n C k o) := by
  intro o
  induction o using Nat.strong_induction_on with
  | _ o ih =>
    intro hc
    obtain ⟨hj, k, hko, hmem, h1 | h1⟩ := (inCone_iff n C h o).1 hc
    · subst h1
      exact ⟨o, hmem, hj, Or.inl rfl⟩
    · obtain ⟨k', hm', hk', h2 | h2⟩ := ih k hko h1
      · subst h2
        exact ⟨k', hm', hk', Or.inr (inCone_of_read n C k' o hj hko hmem)⟩
      · exact ⟨k', hm', hk', Or.inr (inCone_trans n C k' k h2 o (inCone_of_read n C k o hj hko hmem))⟩

theorem p40_pos (l : List ℕ) (hl : l.length = 2) (w : ℕ) (hw : w ∈ l) : ∃ t, t < 2 ∧ l.getD t 0 = w := by
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact ⟨0, by omega, rfl⟩
  · exact ⟨1, by omega, rfl⟩

theorem p40_find {n : ℕ} (C : Circuit) (g : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C) :
    ∀ m h, C.gates.length - h = m → PEqualNP.Core.InOutputCone n C h → g ≤ h →
      (∀ x : Fin n → Bool, val (p40cf C g) (List.ofFn x) (n + h) = false) →
      (∀ x : Fin n → Bool, val (p40cf C g) (List.ofFn x) C.output = false) ∨
      ∃ r, r < C.gates.length ∧ g < r ∧ (gateAt C r).op = GateOp.or ∧ ∃ t, t < 2 ∧
        ∀ x : Fin n → Bool, val (p40cf C g) (List.ofFn x) ((gateAt C r).inputs.getD t 0) = false := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro h hm hoc hgh hz
    obtain ⟨hh, ho | ⟨hno, hc⟩⟩ := hoc
    · left
      intro x
      rw [ho]
      exact hz x
    · obtain ⟨k, hmem, hk, hko⟩ := p40_reader n C h _ hc
      have hlt := isAO2_rb hAO hk hmem
      have hlen : (gateAt C k).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hk)
      obtain ⟨t, ht, hpos⟩ := p40_pos _ hlen _ hmem
      have hkoc : PEqualNP.Core.InOutputCone n C k := by
        show k < C.gates.length ∧ (C.output = n + k ∨
          (n ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone n C k (C.output - n)))
        refine ⟨hk, ?_⟩
        rcases hko with e | e
        · left; omega
        · right; exact ⟨hno, e⟩
      rcases hAO.1 _ (gateAt_mem hk) with hop | hop
      · have hkg : k ≠ g := by omega
        have hzk : ∀ x : Fin n → Bool, val (p40cf C g) (List.ofFn x) (n + k) = false := by
          intro x
          rw [p40_and C g hAO _ (by simp) k hk hkg hop]
          rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
          · rw [hpos, hz x]; rfl
          · rw [hpos, hz x]; simp
        exact ih (C.gates.length - k) (by omega) k rfl hkoc (by omega) hzk
      · right
        refine ⟨k, hk, by omega, hop, t, ht, ?_⟩
        intro x
        rw [hpos]
        exact hz x

theorem p40_ge {n : ℕ} (C : Circuit) (g r y : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hg : g < C.gates.length) (hr : r < C.gates.length) (hgr : g < r) (hy : y < n + r)
    (x : List Bool) (hx : x.length = n)
    (hry : val (p40cf C g) x (n + r) = val (p40cf C g) x y) :
    ∀ i, val (p40cf C g) x i = true →
      val (eraseGate n C r y) x (eraseRedirect n r y i) = true := by
  have hAOE : PEqualNP.TopForm.IsAO2 n (eraseGate n C r y) := p47_isAO2_erase n C r y hr hy hAO
  have hElen := erase_length n C r y hr
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h
    by_cases h1 : i < n + r
    · rw [erase_redirect_lt n r y i h1, erase_val_lt hr hx h1]
      exact p40_le C g hAO hg x hx i h
    by_cases h2 : i = n + r
    · subst h2
      rw [erase_redirect_self, erase_val_lt hr hx hy]
      rw [hry] at h
      exact p40_le C g hAO hg x hx y h
    by_cases h3 : i < n + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j + 1 := ⟨i - n - 1, by omega⟩
      have hj1 : j + 1 < C.gates.length := by omega
      have hrj : r ≤ j := by omega
      rw [erase_redirect_succ n r y (n + j) (by omega)]
      have hjE : j < (eraseGate n C r y).gates.length := by omega
      have hgE : gateAt (eraseGate n C r y) j = erase_rg (eraseRedirect n r y) (gateAt C (j + 1)) :=
        erase_gateAt_ge n C r y j hr hrj hj1
      have hlen : (gateAt C (j + 1)).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj1)
      have e0 : (gateAt (eraseGate n C r y) j).inputs.getD 0 0 =
          eraseRedirect n r y ((gateAt C (j + 1)).inputs.getD 0 0) := by
        rw [hgE]; exact p47_map_getD _ _ 0 (by omega)
      have e1 : (gateAt (eraseGate n C r y) j).inputs.getD 1 0 =
          eraseRedirect n r y ((gateAt C (j + 1)).inputs.getD 1 0) := by
        rw [hgE]; exact p47_map_getD _ _ 1 (by omega)
      have eop : (gateAt (eraseGate n C r y) j).op = (gateAt C (j + 1)).op := by rw [hgE]; rfl
      have l0 := isAO2_rb hAO hj1 (p47_mem2 _ hlen 0 (by omega))
      have l1 := isAO2_rb hAO hj1 (p47_mem2 _ hlen 1 (by omega))
      have hjg : j + 1 ≠ g := by omega
      have hCi : n + j + 1 = n + (j + 1) := by omega
      rw [hCi] at h
      rcases hAO.1 _ (gateAt_mem hj1) with hop | hop
      · rw [p40_and C g hAO x hx (j + 1) hj1 hjg hop, Bool.and_eq_true] at h
        rw [and_val n _ hAOE x hx j hjE (by rw [eop]; exact hop), e0, e1, Bool.and_eq_true]
        exact ⟨ih _ (by omega) h.1, ih _ (by omega) h.2⟩
      · rw [p40_or C g hAO x hx (j + 1) hj1 hjg hop, Bool.or_eq_true] at h
        rw [or_val n _ hAOE x hx j hjE (by rw [eop]; exact hop), e0, e1, Bool.or_eq_true]
        rcases h with h | h
        · exact Or.inl (ih _ (by omega) h)
        · exact Or.inr (ih _ (by omega) h)
    · rw [val_ge (C := p40cf C g) hx (by rw [p40_len]; omega)] at h
      exact absurd h (by simp)

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) → (∀ w : Fin n, PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.SplitCount.unitInput w) = false) → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u z : Fin n, G.Adj u z → (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 0) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 1) (PEqualNP.SplitCount.unitInput z) = true) ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 1) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 0) (PEqualNP.SplitCount.unitInput z) = true) → PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput u z) = false) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  intro n G _ C s g hbip h4c hAO hF hLF hNB hcone hg hgop hgnb hbelow hunit0 hkey
  have hxl : ∀ y : Fin n → Bool, (List.ofFn y).length = n := fun y => by simp
  have hout : ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output g := by
    intro hr
    apply hgnb
    unfold PEqualNP.TopForm.BelowF
    intro y hy
    rw [← hF]
    exact reach_up n C _ (by simp) g hy _ hr
  have hCf : ∀ x : Fin n → Bool, val (p40cf C g) (List.ofFn x) C.output = graphFun G ∅ x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      rw [← hF]
      exact p40_le C g hAO hg _ (hxl x) _ h
    · intro h
      have h' : ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true := by
        unfold graphFun at h
        simpa using h
      obtain ⟨u, z, hadj, hxu, hxz⟩ := h'
      have hle : ∀ i : Fin n, PEqualNP.EdgeOwnership.pairInput u z i = true → x i = true := by
        intro i hi
        simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hi
        rcases hi with hi | hi
        · rw [hi]; exact hxu
        · rw [hi]; exact hxz
      refine mono n (p40cf C g) (p40_aoo C g hAO.1) (PEqualNP.EdgeOwnership.pairInput u z) x hle
        C.output ?_
      have hCe : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) C.output = true := by
        show circuitFun n C (PEqualNP.EdgeOwnership.pairInput u z) = true
        rw [hF]
        unfold graphFun
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        right
        exact ⟨u, z, hadj, by simp [PEqualNP.EdgeOwnership.pairInput],
          by simp [PEqualNP.EdgeOwnership.pairInput]⟩
      cases hge : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g)
      · rw [p40_eq_all C g hAO hg _ (hxl _) hge]
        exact hCe
      · rw [p40_eq_reach G C g u z hAO hLF hcone hbelow hg hNB hgnb hkey hadj hge C.output hout]
        exact hCe
  rcases p40_find C g hAO _ g rfl (hcone g hg) (le_refl g)
      (fun x => p40_self C g hg _ (hxl x)) with hz | ⟨r, hr, hgr, hrop, t, ht, hw⟩
  · refine ⟨⟨[], n⟩, ⟨fun gt h => by simp at h, fun j hj => by simp at hj, fun gt h => by simp at h⟩,
      by show 0 < C.gates.length; omega, ?_⟩
    funext x
    rw [← hCf x, hz x]
    show val (⟨[], n⟩ : Circuit) (List.ofFn x) n = false
    exact val_ge (hxl x) (by simp)
  · have hlen : (gateAt C r).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hr)
    have hgr' : r ≠ g := by omega
    obtain ⟨y, hy, hry, hyC⟩ : ∃ y, y < n + r ∧
        (∀ x : Fin n → Bool, val (p40cf C g) (List.ofFn x) (n + r) = val (p40cf C g) (List.ofFn x) y) ∧
        (∀ x : Fin n → Bool, val C (List.ofFn x) y = true → val C (List.ofFn x) (n + r) = true) := by
      rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
      · refine ⟨(gateAt C r).inputs.getD 1 0, isAO2_rb hAO hr (p47_mem2 _ hlen 1 (by omega)), ?_, ?_⟩
        · intro x
          rw [p40_or C g hAO _ (hxl x) r hr hgr' hrop, hw x]
          rfl
        · intro x hx
          rw [or_val n C hAO _ (hxl x) r hr hrop, hx]
          simp
      · refine ⟨(gateAt C r).inputs.getD 0 0, isAO2_rb hAO hr (p47_mem2 _ hlen 0 (by omega)), ?_, ?_⟩
        · intro x
          rw [p40_or C g hAO _ (hxl x) r hr hgr' hrop, hw x]
          simp
        · intro x hx
          rw [or_val n C hAO _ (hxl x) r hr hrop, hx]
          rfl
    refine ⟨eraseGate n C r y, p47_isAO2_erase n C r y hr hy hAO,
      by have := erase_size n C r y hr; omega, ?_⟩
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      have hrel := erase_val_rel (fun op => op = GateOp.and ∨ op = GateOp.or)
        (fun a b => b = true → a = true) (fun b hb => hb) hr hy
        (fun op l f f' hq h => by
          show op.eval ((l.map (eraseRedirect n r y)).map f') = true → op.eval (l.map f) = true
          rw [List.map_map]
          exact opMono_imp op hq l (f' ∘ eraseRedirect n r y) f (fun i _ => h i))
        (fun gt hgt => hAO.1 gt (List.mem_of_mem_drop hgt)) (hxl x)
        (hyC x) C.output
      rw [← hF]
      apply hrel
      show val (eraseGate n C r y) (List.ofFn x) (eraseRedirect n r y C.output) = true
      rw [← erase_output n C r y hr]
      exact h
    · intro h
      rw [← hCf x] at h
      have h2 := p40_ge C g r y hAO hg hr hgr hy _ (hxl x) (hry x) C.output h
      show val (eraseGate n C r y) (List.ofFn x) (eraseGate n C r y).output = true
      rw [erase_output n C r y hr]
      exact h2


theorem edge_invisible_gate_removable (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hF : circuitFun n C = graphFun G ∅)
    (hcone : PEqualNP.Core.InOutputCone n C g) (hg : g < C.gates.length)
    (hzero : ∀ u z : Fin n, G.Adj u z →
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g) = false) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧
      circuitFun n D = graphFun G ∅ := by
  have hxl : ∀ y : Fin n → Bool, (List.ofFn y).length = n := fun y => by simp
  have hCf : ∀ x : Fin n → Bool, val (p40cf C g) (List.ofFn x) C.output = graphFun G ∅ x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      rw [← hF]
      exact p40_le C g hAO hg _ (hxl x) _ h
    · intro h
      have h' : ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true := by
        unfold graphFun at h
        simpa using h
      obtain ⟨u, z, hadj, hxu, hxz⟩ := h'
      have hle : ∀ i : Fin n, PEqualNP.EdgeOwnership.pairInput u z i = true → x i = true := by
        intro i hi
        simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hi
        rcases hi with hi | hi
        · rw [hi]; exact hxu
        · rw [hi]; exact hxz
      refine mono n (p40cf C g) (p40_aoo C g hAO.1) (PEqualNP.EdgeOwnership.pairInput u z) x hle
        C.output ?_
      rw [p40_eq_all C g hAO hg _ (hxl _) (hzero u z hadj)]
      show circuitFun n C (PEqualNP.EdgeOwnership.pairInput u z) = true
      rw [hF]
      unfold graphFun
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      right
      exact ⟨u, z, hadj, by simp [PEqualNP.EdgeOwnership.pairInput],
        by simp [PEqualNP.EdgeOwnership.pairInput]⟩
  rcases p40_find C g hAO _ g rfl hcone (le_refl g)
      (fun x => p40_self C g hg _ (hxl x)) with hz | ⟨r, hr, hgr, hrop, t, ht, hw⟩
  · refine ⟨⟨[], n⟩, ⟨fun gt h => by simp at h, fun j hj => by simp at hj, fun gt h => by simp at h⟩,
      by show 0 < C.gates.length; omega, ?_⟩
    funext x
    rw [← hCf x, hz x]
    show val (⟨[], n⟩ : Circuit) (List.ofFn x) n = false
    exact val_ge (hxl x) (by simp)
  · have hlen : (gateAt C r).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hr)
    have hgr' : r ≠ g := by omega
    obtain ⟨y, hy, hry, hyC⟩ : ∃ y, y < n + r ∧
        (∀ x : Fin n → Bool, val (p40cf C g) (List.ofFn x) (n + r) = val (p40cf C g) (List.ofFn x) y) ∧
        (∀ x : Fin n → Bool, val C (List.ofFn x) y = true → val C (List.ofFn x) (n + r) = true) := by
      rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
      · refine ⟨(gateAt C r).inputs.getD 1 0, isAO2_rb hAO hr (p47_mem2 _ hlen 1 (by omega)), ?_, ?_⟩
        · intro x
          rw [p40_or C g hAO _ (hxl x) r hr hgr' hrop, hw x]
          rfl
        · intro x hx
          rw [or_val n C hAO _ (hxl x) r hr hrop, hx]
          simp
      · refine ⟨(gateAt C r).inputs.getD 0 0, isAO2_rb hAO hr (p47_mem2 _ hlen 0 (by omega)), ?_, ?_⟩
        · intro x
          rw [p40_or C g hAO _ (hxl x) r hr hgr' hrop, hw x]
          simp
        · intro x hx
          rw [or_val n C hAO _ (hxl x) r hr hrop, hx]
          rfl
    refine ⟨eraseGate n C r y, p47_isAO2_erase n C r y hr hy hAO,
      by have := erase_size n C r y hr; omega, ?_⟩
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      have hrel := erase_val_rel (fun op => op = GateOp.and ∨ op = GateOp.or)
        (fun a b => b = true → a = true) (fun b hb => hb) hr hy
        (fun op l f f' hq h => by
          show op.eval ((l.map (eraseRedirect n r y)).map f') = true → op.eval (l.map f) = true
          rw [List.map_map]
          exact opMono_imp op hq l (f' ∘ eraseRedirect n r y) f (fun i _ => h i))
        (fun gt hgt => hAO.1 gt (List.mem_of_mem_drop hgt)) (hxl x)
        (hyC x) C.output
      rw [← hF]
      apply hrel
      show val (eraseGate n C r y) (List.ofFn x) (eraseRedirect n r y C.output) = true
      rw [← erase_output n C r y hr]
      exact h
    · intro h
      rw [← hCf x] at h
      have h2 := p40_ge C g r y hAO hg hr hgr hy _ (hxl x) (hry x) C.output h
      show val (eraseGate n C r y) (List.ofFn x) (eraseGate n C r y).output = true
      rw [erase_output n C r y hr]
      exact h2

theorem least_gate_has_edge (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hF : circuitFun n C = graphFun G ∅)
    (hcone : PEqualNP.Core.InOutputCone n C g) (hg : g < C.gates.length)
    (hmin : ∀ D : Circuit, PEqualNP.TopForm.IsAO2 n D → circuitFun n D = graphFun G ∅ →
      C.size ≤ D.size) :
    ∃ u z : Fin n, G.Adj u z ∧
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g) = true := by
  by_contra h
  push_neg at h
  have hzero : ∀ u z : Fin n, G.Adj u z →
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g) = false := by
    intro u z hadj
    exact Bool.eq_false_iff.mpr (h u z hadj)
  obtain ⟨D, hD, hsize, hfun⟩ := edge_invisible_gate_removable n G C g hAO hF hcone hg hzero
  have := hmin D hD hfun
  omega


theorem edge_equiv_smaller_replacement (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g y : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hF : circuitFun n C = graphFun G ∅) (hg : g < C.gates.length) (hy : y < n + g)
    (hbelow : ∀ x : Fin n → Bool, val C (List.ofFn x) y = true →
      val C (List.ofFn x) (n + g) = true)
    (hedge : ∀ u z : Fin n, G.Adj u z →
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) y =
        val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g)) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧
      circuitFun n D = graphFun G ∅ := by
  let D := eraseGate n C g y
  have hD : PEqualNP.TopForm.IsAO2 n D := p47_isAO2_erase n C g y hg hy hAO
  have hxl : ∀ x : Fin n → Bool, (List.ofFn x).length = n := fun x => by simp
  refine ⟨D, hD, by have := erase_size n C g y hg; dsimp [D]; omega, ?_⟩
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    have hrel := erase_val_rel (fun op => op = GateOp.and ∨ op = GateOp.or)
      (fun a b => b = true → a = true) (fun b hb => hb) hg hy
      (fun op l f f' hq h => by
        show op.eval ((l.map (eraseRedirect n g y)).map f') = true → op.eval (l.map f) = true
        rw [List.map_map]
        exact opMono_imp op hq l (f' ∘ eraseRedirect n g y) f (fun i _ => h i))
      (fun gt hgt => hAO.1 gt (List.mem_of_mem_drop hgt)) (hxl x)
      (hbelow x) C.output
    rw [← hF]
    apply hrel
    show val D (List.ofFn x) (eraseRedirect n g y C.output) = true
    rw [← erase_output n C g y hg]
    exact hx
  · intro hx
    have he : ∃ u z : Fin n, G.Adj u z ∧ x u = true ∧ x z = true := by
      unfold graphFun at hx
      simpa using hx
    obtain ⟨u, z, hadj, hxu, hxz⟩ := he
    have hle : ∀ i : Fin n, PEqualNP.EdgeOwnership.pairInput u z i = true → x i = true := by
      intro i hi
      simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · exact hxu
      · exact hxz
    apply mono n D hD.1 (PEqualNP.EdgeOwnership.pairInput u z) x hle D.output
    have hCe : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) C.output = true := by
      show circuitFun n C (PEqualNP.EdgeOwnership.pairInput u z) = true
      rw [hF]
      unfold graphFun
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      right
      exact ⟨u, z, hadj, by simp [PEqualNP.EdgeOwnership.pairInput],
        by simp [PEqualNP.EdgeOwnership.pairInput]⟩
    have hrel := erase_val_rel (fun _ => True) (fun a b => a = b) (fun b => rfl) hg hy
      (fun op l f f' _ h => by
        rw [List.map_map]
        congr 1
        exact List.map_congr_left (fun i _ => h i))
      (fun _ _ => True.intro) (hxl (PEqualNP.EdgeOwnership.pairInput u z))
      (hedge u z hadj).symm C.output
    change val D (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z))
      (eraseGate n C g y).output = true
    rw [erase_output n C g y hg, ← hrel]
    exact hCe

theorem least_gate_separates_earlier (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g y : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hF : circuitFun n C = graphFun G ∅) (hg : g < C.gates.length) (hy : y < n + g)
    (hmin : ∀ D : Circuit, PEqualNP.TopForm.IsAO2 n D → circuitFun n D = graphFun G ∅ →
      C.size ≤ D.size)
    (hbelow : ∀ x : Fin n → Bool, val C (List.ofFn x) y = true →
      val C (List.ofFn x) (n + g) = true) :
    ∃ u z : Fin n, G.Adj u z ∧
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g) = true ∧
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) y = false := by
  by_contra h
  push_neg at h
  have hedge : ∀ u z : Fin n, G.Adj u z →
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) y =
        val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g) := by
    intro u z hadj
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact hbelow (PEqualNP.EdgeOwnership.pairInput u z)
    · intro hg'
      exact Bool.eq_true_of_ne_false (h u z hadj hg')
  obtain ⟨D, hD, hsize, hfun⟩ := edge_equiv_smaller_replacement n G C g y hAO hF hg hy hbelow hedge
  have := hmin D hD hfun
  omega

lemma singleton_overlap_on_edge {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (u : Fin n) (huA : u ∈ A) (huB : u ∈ B)
    (hinter : ∀ v, v ∈ A → v ∈ B → v = u)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b → a = u ∨ b = u)
    (a b : Fin n) (hab : G.Adj a b) :
    ((a ∈ A ∨ b ∈ A) ∧ (a ∈ B ∨ b ∈ B)) ↔ a = u ∨ b = u := by
  constructor
  · rintro ⟨ha | hb, ha' | hb'⟩
    · exact Or.inl (hinter a ha ha')
    · exact hcross a ha b hb' hab
    · exact (hcross b hb a ha' hab.symm).symm
    · exact Or.inr (hinter b hb hb')
  · rintro (rfl | rfl) <;> simp [huA, huB]


def patchGate (C : Circuit) (g : ℕ) (fresh : Gate) : Circuit :=
  ⟨C.gates.set g fresh, C.output⟩

lemma patch_length (C : Circuit) (g : ℕ) (fresh : Gate) :
    (patchGate C g fresh).gates.length = C.gates.length := by simp [patchGate]

lemma patch_gate_other (C : Circuit) (g j : ℕ) (fresh : Gate) (h : g ≠ j) :
    gateAt (patchGate C g fresh) j = gateAt C j := by
  simp [patchGate, gateAt, List.getD_eq_getElem?_getD, h]

lemma patch_gate_self (C : Circuit) (g : ℕ) (fresh : Gate) (hg : g < C.gates.length) :
    gateAt (patchGate C g fresh) g = fresh := by
  simp [patchGate, gateAt, List.getD_eq_getElem?_getD, hg]

lemma patch_isAO2 (n : ℕ) (C : Circuit) (g : ℕ) (fresh : Gate)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hg : g < C.gates.length)
    (hop : fresh.op = GateOp.and ∨ fresh.op = GateOp.or)
    (hlen : fresh.inputs.length = 2) (hback : ∀ i ∈ fresh.inputs, i < n + g) :
    PEqualNP.TopForm.IsAO2 n (patchGate C g fresh) := by
  refine ⟨?_, ?_, ?_⟩
  · intro gt hgt
    rcases List.mem_or_eq_of_mem_set hgt with h | rfl
    · exact hAO.1 gt h
    · exact hop
  · intro j hj
    have hjC : j < C.gates.length := by simpa [patchGate] using hj
    change ∀ i ∈ (gateAt (patchGate C g fresh) j).inputs, i < n + j
    by_cases h : j = g
    · subst j
      rw [patch_gate_self C g fresh hg]
      exact hback
    · rw [patch_gate_other C g j fresh (Ne.symm h)]
      exact hAO.2.1 j hjC
  · intro gt hgt
    rcases List.mem_or_eq_of_mem_set hgt with h | rfl
    · exact hAO.2.2 gt h
    · exact hlen

lemma patch_eq_before (n : ℕ) (C : Circuit) (g : ℕ) (fresh : Gate)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hg : g < C.gates.length)
    (x : List Bool) (hx : x.length = n) :
    ∀ i, i < n + g → val (patchGate C g fresh) x i = val C x i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hinput : i < n
    · rw [val_input hx hinput, val_input hx hinput]
    obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
    have hj : j < C.gates.length := by omega
    have hjp : j < (patchGate C g fresh).gates.length := by rw [patch_length]; exact hj
    rw [val_gate hx hjp, patch_gate_other C g j fresh (by omega), val_gate hx hj]
    congr 1
    apply List.map_congr_left
    intro k hk
    have hb := hAO.2.1 j hj k hk
    simp only [if_pos hb]
    exact ih k hb (by omega)

lemma patch_val_self (n : ℕ) (C : Circuit) (g : ℕ) (fresh : Gate)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hg : g < C.gates.length)
    (hback : ∀ i ∈ fresh.inputs, i < n + g) (x : List Bool) (hx : x.length = n) :
    val (patchGate C g fresh) x (n + g) = fresh.op.eval (fresh.inputs.map (val C x)) := by
  rw [val_gate hx (by rw [patch_length]; exact hg), patch_gate_self C g fresh hg]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hb := hback i hi
  simp only [if_pos hb]
  exact patch_eq_before n C g fresh hAO hg x hx i hb

lemma patch_val_rel (n : ℕ) (C : Circuit) (g : ℕ) (fresh : Gate)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hg : g < C.gates.length)
    (hback : ∀ i ∈ fresh.inputs, i < n + g) (x : List Bool) (hx : x.length = n)
    (R : Bool → Bool → Prop) (hrefl : ∀ b, R b b) (hmono : OpMono R)
    (hgate : R (val C x (n + g)) (fresh.op.eval (fresh.inputs.map (val C x)))) :
    ∀ i, R (val C x i) (val (patchGate C g fresh) x i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hinput : i < n
    · rw [val_input hx hinput, val_input hx hinput]
      exact hrefl _
    by_cases hin : i < n + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      have hj : j < C.gates.length := by omega
      by_cases hjg : j = g
      · subst j
        rw [patch_val_self n C g fresh hAO hg hback x hx]
        exact hgate
      have hjp : j < (patchGate C g fresh).gates.length := by rw [patch_length]; exact hj
      rw [val_gate hx hj, val_gate hx hjp, patch_gate_other C g j fresh (Ne.symm hjg)]
      apply hmono _ (hAO.1 _ (gateAt_mem hj))
      intro k hk
      have hb := hAO.2.1 j hj k hk
      simp only [if_pos hb]
      exact ih k hb
    · rw [val_ge hx (by omega), val_ge (C := patchGate C g fresh) hx
        (by rw [patch_length]; omega)]
      exact hrefl _

lemma patch_opMono_eq : OpMono (fun a b => a = b) := by
  intro op _ l f f' h
  congr 1
  exact List.map_congr_left h

theorem patch_below_target (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (fresh : Gate) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hF : circuitFun n C = graphFun G ∅) (hg : g < C.gates.length)
    (hop : fresh.op = GateOp.and ∨ fresh.op = GateOp.or)
    (hlen : fresh.inputs.length = 2) (hback : ∀ i ∈ fresh.inputs, i < n + g)
    (hold : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + g) = true → graphFun G ∅ x = true)
    (hnew : ∀ x : Fin n → Bool,
      fresh.op.eval (fresh.inputs.map (val C (List.ofFn x))) = true → graphFun G ∅ x = true)
    (hedge : ∀ u z : Fin n, G.Adj u z →
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g) = true →
      fresh.op.eval (fresh.inputs.map (val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)))) = true) :
    PEqualNP.TopForm.IsAO2 n (patchGate C g fresh) ∧ (patchGate C g fresh).size = C.size ∧
      circuitFun n (patchGate C g fresh) = graphFun G ∅ := by
  have hD := patch_isAO2 n C g fresh hAO hg hop hlen hback
  refine ⟨hD, by simp [patchGate, Circuit.size], ?_⟩
  funext x
  cases hFx : graphFun G ∅ x with
  | false =>
    have hgo : val C (List.ofFn x) (n + g) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have := hold x h
      simp [hFx] at this
    have hgn : fresh.op.eval (fresh.inputs.map (val C (List.ofFn x))) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have := hnew x h
      simp [hFx] at this
    have heq := patch_val_rel n C g fresh hAO hg hback (List.ofFn x) (by simp)
      (fun a b => a = b) (fun b => rfl) patch_opMono_eq (by rw [hgo, hgn]) C.output
    change val (patchGate C g fresh) (List.ofFn x) C.output = false
    rw [← heq]
    change circuitFun n C x = false
    rw [hF, hFx]
  | true =>
    have he : ∃ u z : Fin n, G.Adj u z ∧ x u = true ∧ x z = true := by
      unfold graphFun at hFx
      simpa using hFx
    obtain ⟨u, z, hadj, hxu, hxz⟩ := he
    have hle : ∀ i : Fin n, PEqualNP.EdgeOwnership.pairInput u z i = true → x i = true := by
      intro i hi
      simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · exact hxu
      · exact hxz
    apply mono n (patchGate C g fresh) hD.1 (PEqualNP.EdgeOwnership.pairInput u z) x hle C.output
    apply patch_val_rel n C g fresh hAO hg hback
      (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (by simp)
      (fun a b => a = true → b = true) (fun b hb => hb) opMono_imp (hedge u z hadj) C.output
    change circuitFun n C (PEqualNP.EdgeOwnership.pairInput u z) = true
    rw [hF]
    unfold graphFun
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    right
    exact ⟨u, z, hadj, by simp [PEqualNP.EdgeOwnership.pairInput],
      by simp [PEqualNP.EdgeOwnership.pairInput]⟩

end PEqualNP.Outside.L_meta_2583_aux.EdgeInvisible

namespace PEqualNP.Outside.L_meta_2583.PlaneGeometry

lemma lines_intersect {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (l m : Fin N) (hne : l ≠ m) : ∃! p : Fin N, I p l ∧ I p m := by
  let P := Finset.univ.filter (fun p => I p l)
  let family := fun p : Fin N => (Finset.univ.filter (fun k => I p k)).erase l
  have disjoint : (P : Set (Fin N)).PairwiseDisjoint family := by
    intro p hp p' hp' hpp
    apply Finset.disjoint_left.mpr
    intro k hk hk'
    have pk : I p k := (Finset.mem_filter.mp (Finset.mem_erase.mp hk).2).2
    have p'k : I p' k := (Finset.mem_filter.mp (Finset.mem_erase.mp hk').2).2
    have pl : I p l := (Finset.mem_filter.mp hp).2
    have p'l : I p' l := (Finset.mem_filter.mp hp').2
    exact (Finset.ne_of_mem_erase hk) ((hu p p' hpp).unique ⟨pk, p'k⟩ ⟨pl, p'l⟩)
  have each : ∀ p ∈ P, (family p).card = q := by
    intro p hp
    rw [Finset.card_erase_of_mem (by simpa [P] using hp), lines_through q N I hq hN hl hu p]
    rfl
  have card : (P.biUnion family).card = (Finset.univ.erase l).card := by
    rw [Finset.card_biUnion disjoint, Finset.sum_congr rfl each, Finset.sum_const,
      smul_eq_mul, show P.card = q + 1 from hl l,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, hN]
    rw [Nat.add_sub_cancel]
    ring
  have sub : P.biUnion family ⊆ Finset.univ.erase l := by
    intro k hk
    obtain ⟨p, hp, hk⟩ := Finset.mem_biUnion.mp hk
    exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hk, Finset.mem_univ _⟩
  have same := Finset.eq_of_subset_of_card_le sub card.ge
  have mm : m ∈ P.biUnion family := by rw [same]; simp [hne.symm]
  obtain ⟨p, hp, hm⟩ := Finset.mem_biUnion.mp mm
  have pl : I p l := (Finset.mem_filter.mp hp).2
  have pm : I p m := (Finset.mem_filter.mp (Finset.mem_erase.mp hm).2).2
  refine ⟨p, ⟨pl, pm⟩, ?_⟩
  intro p' h'
  by_contra diff
  exact hne ((hu p' p diff).unique ⟨h'.1, pl⟩ ⟨h'.2, pm⟩)

lemma regular_independent_bound {N d : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (U V S T : Finset (Fin N)) (hd : 0 < d) (hS : S ⊆ U) (hT : T ⊆ V)
    (rows : ∀ p ∈ U, (V.filter (fun l => I p l)).card = d)
    (cols : ∀ l ∈ V, (U.filter (fun p => I p l)).card = d)
    (none : ∀ p ∈ S, ∀ l ∈ T, ¬ I p l) : S.card + T.card ≤ V.card := by
  have left : ((S ×ˢ V).filter (fun e : Fin N × Fin N => I e.1 e.2)).card = S.card * d := by
    rw [cardL, Finset.sum_congr rfl (fun p hp => rows p (hS hp)), Finset.sum_const, smul_eq_mul]
  have right : ((U ×ˢ (V \ T)).filter (fun e : Fin N × Fin N => I e.1 e.2)).card = (V \ T).card * d := by
    rw [cardR, Finset.sum_congr rfl (fun l hl => cols l (Finset.mem_sdiff.mp hl).1),
      Finset.sum_const, smul_eq_mul]
  have sub : (S ×ˢ V).filter (fun e : Fin N × Fin N => I e.1 e.2) ⊆
      (U ×ˢ (V \ T)).filter (fun e : Fin N × Fin N => I e.1 e.2) := by
    rintro ⟨p, l⟩ h
    obtain ⟨hmem, hi⟩ := Finset.mem_filter.mp h
    obtain ⟨hp, hl⟩ := Finset.mem_product.mp hmem
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hS hp, ?_⟩, hi⟩
    exact Finset.mem_sdiff.mpr ⟨hl, fun ht => none p hp l ht hi⟩
  have bound := Finset.card_le_card sub
  rw [left, right] at bound
  have cb := Nat.le_of_mul_le_mul_right bound hd
  rw [Finset.card_sdiff_of_subset hT] at cb
  have tc := Finset.card_le_card hT
  omega

lemma residual_degrees {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p l : Fin N) (outside : ¬ I p l) :
    let U := (Finset.univ.filter (fun x => ¬ I x l)).erase p
    let V := (Finset.univ.filter (fun m => ¬ I p m)).erase l
    (∀ x ∈ U, (V.filter (fun m => I x m)).card = q) ∧
    (∀ m ∈ V, (U.filter (fun x => I x m)).card = q) := by
  dsimp
  constructor
  · intro x hx
    have xp : x ≠ p := Finset.ne_of_mem_erase hx
    have xl : ¬ I x l := (Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).2
    obtain ⟨m, hm, unique⟩ := hu x p xp
    have same : (((Finset.univ.filter (fun k => ¬ I p k)).erase l).filter (fun k => I x k)) =
        (Finset.univ.filter (fun k => I x k)).erase m := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨kl, pk⟩, xk⟩
        exact ⟨fun e => pk (e ▸ hm.2), xk⟩
      · rintro ⟨km, xk⟩
        exact ⟨⟨fun e => xl (e ▸ xk), fun pk => km (unique k ⟨xk, pk⟩)⟩, xk⟩
    rw [same, Finset.card_erase_of_mem (by simp [hm.1]), lines_through q N I hq hN hl hu x]
    rfl
  · intro m hm
    have ml : m ≠ l := Finset.ne_of_mem_erase hm
    have pm : ¬ I p m := (Finset.mem_filter.mp (Finset.mem_erase.mp hm).2).2
    obtain ⟨x, hx, unique⟩ := lines_intersect I hq hN hl hu m l ml
    have same : (((Finset.univ.filter (fun y => ¬ I y l)).erase p).filter (fun y => I y m)) =
        (Finset.univ.filter (fun y => I y m)).erase x := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨yp, yl⟩, ym⟩
        exact ⟨fun e => yl (e ▸ hx.2), ym⟩
      · rintro ⟨yx, ym⟩
        exact ⟨⟨fun e => pm (e ▸ ym), fun yl => yx (unique y ⟨ym, yl⟩)⟩, ym⟩
    rw [same, Finset.card_erase_of_mem (by simp [hx.1]), hl m]
    rfl

lemma mixed_independent_bound {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (S T : Finset (Fin N)) (hs : S.Nonempty) (ht : T.Nonempty)
    (none : ∀ p ∈ S, ∀ l ∈ T, ¬ I p l) : S.card + T.card ≤ q ^ 2 + 1 := by
  obtain ⟨p, hp⟩ := hs
  obtain ⟨l, hlT⟩ := ht
  let U := (Finset.univ.filter (fun x => ¬ I x l)).erase p
  let V := (Finset.univ.filter (fun m => ¬ I p m)).erase l
  have outside := none p hp l hlT
  obtain ⟨rows, cols⟩ := residual_degrees I hq hN hl hu p l outside
  have hS : S.erase p ⊆ U := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hx,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, none x (Finset.mem_of_mem_erase hx) l hlT⟩⟩
  have hT : T.erase l ⊆ V := by
    intro m hm
    exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hm,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, none p hp m (Finset.mem_of_mem_erase hm)⟩⟩
  have bound := regular_independent_bound I U V (S.erase p) (T.erase l) hq hS hT rows cols
    (fun x hx m hm => none x (Finset.mem_of_mem_erase hx) m (Finset.mem_of_mem_erase hm))
  have vc : V.card = q ^ 2 - 1 := by
    have count := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (fun m => I p m)
    rw [lines_through q N I hq hN hl hu p, Finset.card_univ, Fintype.card_fin] at count
    rw [Finset.card_erase_of_mem (by simp [outside])]
    omega
  rw [Finset.card_erase_of_mem hp, Finset.card_erase_of_mem hlT, vc] at bound
  have qq : 0 < q ^ 2 := pow_pos hq 2
  have sc := Finset.card_pos.mpr ⟨p, hp⟩
  have tc := Finset.card_pos.mpr ⟨l, hlT⟩
  omega


lemma proper_mixed_cover_bound {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B : Finset (Fin N)) (aProper : A ≠ Finset.univ) (bProper : B ≠ Finset.univ)
    (cover : ∀ p l : Fin N, I p l → p ∈ A ∨ l ∈ B) :
    N + q ≤ A.card + B.card := by
  obtain ⟨p, hp⟩ : ∃ p : Fin N, p ∉ A := by
    by_contra! all
    exact aProper (Finset.eq_univ_of_forall all)
  obtain ⟨l, hlB⟩ : ∃ l : Fin N, l ∉ B := by
    by_contra! all
    exact bProper (Finset.eq_univ_of_forall all)
  have none : ∀ p ∈ Finset.univ \ A, ∀ l ∈ Finset.univ \ B, ¬ I p l := by
    intro x hx y hy hi
    rcases cover x y hi with h | h
    · exact (Finset.mem_sdiff.mp hx).2 h
    · exact (Finset.mem_sdiff.mp hy).2 h
  have bound := mixed_independent_bound I hq hN hl hu (Finset.univ \ A) (Finset.univ \ B)
    ⟨p, by simp [hp]⟩ ⟨l, by simp [hlB]⟩ none
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ A),
    Finset.card_sdiff_of_subset (Finset.subset_univ B), Finset.card_univ, Fintype.card_fin] at bound
  have aCard : A.card ≤ N := by simpa using Finset.card_le_card (Finset.subset_univ A)
  have bCard : B.card ≤ N := by simpa using Finset.card_le_card (Finset.subset_univ B)
  omega

lemma proper_mixed_cover_pays_debt {q N s : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B : Finset (Fin N)) (aProper : A ≠ Finset.univ) (bProper : B ≠ Finset.univ)
    (cover : ∀ p l : Fin N, I p l → p ∈ A ∨ l ∈ B)
    (cost : (edges I).card + A.card + B.card ≤ s + 1 + q) :
    N * (q + 2) ≤ s + 1 := by
  have gap := proper_mixed_cover_bound I hq hN hl hu A B aProper bProper cover
  rw [edges_card I hl] at cost
  have expand : N * (q + 2) = N * (q + 1) + N := by ring
  omega

end PEqualNP.Outside.L_meta_2583.PlaneGeometry


namespace PEqualNP.Outside.L_meta_2583.RectangleLayer

lemma rectangle_split (p l a b : Bool)
    (hp : p = true → a = true) (hl : l = true → b = true) :
    ((a && b) && (p || l)) = ((p && b) || (l && a)) := by
  cases p <;> cases l <;> simp_all

lemma rectangle_family_split (p l : Bool) (xs : List (Bool × Bool))
    (hp : ∀ x ∈ xs, p = true → x.1 = true)
    (hl : ∀ x ∈ xs, l = true → x.2 = true) :
    ((xs.any fun x => x.1 && x.2) && (p || l)) =
      ((p && xs.any Prod.snd) || (l && xs.any Prod.fst)) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := rectangle_split p l x.1 x.2 (hp x (by simp)) (hl x (by simp))
    have hi := ih (fun y hy => hp y (by simp [hy])) (fun y hy => hl y (by simp [hy]))
    simp only [List.any_cons]
    have distrib (a b c : Bool) : ((a || b) && c) = ((a && c) || (b && c)) := by
      cases a <;> cases b <;> cases c <;> rfl
    rw [distrib, hx, hi]
    cases p <;> cases l <;> simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

lemma shared_centre_projection (p : Bool) (xs : List (Bool × Bool))
    (hp : ∀ x ∈ xs, p = true → x.1 = true) :
    (p && (xs.any fun x => x.1 && x.2)) = (p && xs.any Prod.snd) := by
  cases p
  · simp
  · simp only [Bool.true_and]
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      rw [List.any_cons, List.any_cons, hp x (by simp) rfl]
      simp only [Bool.true_and]
      rw [ih (fun y hy => hp y (by simp [hy]))]

lemma distinct_pair_selectors {P L : Type} [DecidableEq P] [DecidableEq L]
    (p p' : P) (l l' : L) (S : Finset (Sum P L))
    (hne : p ≠ p' ∨ l ≠ l')
    (hleft : ∀ x ∈ S, x = Sum.inl p ∨ x = Sum.inr l)
    (hright : ∀ x ∈ S, x = Sum.inl p' ∨ x = Sum.inr l') :
    S.card ≤ 1 := by
  rcases hne with hpp | hll
  · have hs : S ⊆ {Sum.inr l} := by
      intro x hx
      apply Finset.mem_singleton.mpr
      rcases hleft x hx with rfl | he
      · rcases hright (Sum.inl p) hx with he | he
        · exact False.elim (hpp (Sum.inl.inj he))
        · cases he
      · exact he
    exact (Finset.card_le_card hs).trans_eq (Finset.card_singleton _)
  · have hs : S ⊆ {Sum.inl p} := by
      intro x hx
      apply Finset.mem_singleton.mpr
      rcases hleft x hx with he | rfl
      · exact he
      · rcases hright (Sum.inr l) hx with he | he
        · cases he
        · exact False.elim (hll (Sum.inr.inj he))
    exact (Finset.card_le_card hs).trans_eq (Finset.card_singleton _)

end PEqualNP.Outside.L_meta_2583.RectangleLayer


namespace PEqualNP.Outside.L_meta_2583.TwoRectangles

lemma one_side_incident {α β : Type} [DecidableEq α] [DecidableEq β]
    (I : α → β → Prop) (P₁ P₂ : Finset α) (L₁ L₂ : Finset β)
    (below : ∀ (X : Finset α) (Y : Finset β),
      (P₁ ∩ X).Nonempty → (P₂ ∩ X).Nonempty →
      (L₁ ∩ Y).Nonempty → (L₂ ∩ Y).Nonempty → ∃ p ∈ X, ∃ l ∈ Y, I p l)
    (p : α) (hp₁ : p ∈ P₁) (hp₂ : p ∈ P₂) :
    (∀ l ∈ L₁, I p l) ∨ (∀ l ∈ L₂, I p l) := by
  classical
  by_cases first : ∀ l ∈ L₁, I p l
  · exact Or.inl first
  right
  by_contra second
  push Not at first second
  obtain ⟨l₁, hl₁, hn₁⟩ := first
  obtain ⟨l₂, hl₂, hn₂⟩ := second
  obtain ⟨u, hu, v, hv, incident⟩ := below {p} {l₁, l₂}
    ⟨p, by simp [hp₁]⟩ ⟨p, by simp [hp₂]⟩
    ⟨l₁, by simp [hl₁]⟩ ⟨l₂, by simp [hl₂]⟩
  have same : u = p := Finset.mem_singleton.mp hu
  subst u
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact hn₁ incident
  · exact hn₂ incident

lemma star_replacement {α β : Type} [DecidableEq α] [DecidableEq β]
    (I : α → β → Prop) (P₁ P₂ : Finset α) (L₁ L₂ : Finset β)
    (noRectangle : ∀ p p' l l', p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (below : ∀ (X : Finset α) (Y : Finset β),
      (P₁ ∩ X).Nonempty → (P₂ ∩ X).Nonempty →
      (L₁ ∩ Y).Nonempty → (L₂ ∩ Y).Nonempty → ∃ p ∈ X, ∃ l ∈ Y, I p l)
    (pointEdge : (P₁ ∩ P₂).Nonempty) (lineEdge : (L₁ ∩ L₂).Nonempty) :
    (∃ p, P₁ ∩ P₂ = {p} ∧ ((∀ l ∈ L₁, I p l) ∨ (∀ l ∈ L₂, I p l))) ∨
    (∃ l, L₁ ∩ L₂ = {l} ∧ ((∀ p ∈ P₁, I p l) ∨ (∀ p ∈ P₂, I p l))) := by
  classical
  have commonIncident : ∀ p ∈ P₁ ∩ P₂, ∀ l ∈ L₁ ∩ L₂, I p l := by
    intro p hp l hl
    have hp₁ := (Finset.mem_inter.mp hp).1
    have hp₂ := (Finset.mem_inter.mp hp).2
    have hl₁ := (Finset.mem_inter.mp hl).1
    have hl₂ := (Finset.mem_inter.mp hl).2
    obtain ⟨u, hu, v, hv, hit⟩ := below {p} {l}
      ⟨p, by simp [hp₁]⟩ ⟨p, by simp [hp₂]⟩
      ⟨l, by simp [hl₁]⟩ ⟨l, by simp [hl₂]⟩
    have hu' := Finset.mem_singleton.mp hu
    have hv' := Finset.mem_singleton.mp hv
    subst u
    subst v
    exact hit
  obtain ⟨p, hp⟩ := pointEdge
  obtain ⟨l, hl⟩ := lineEdge
  by_cases singleton : P₁ ∩ P₂ = {p}
  · exact Or.inl ⟨p, singleton,
      one_side_incident I P₁ P₂ L₁ L₂ below p
        (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hp).2⟩
  have other : ∃ p' ∈ P₁ ∩ P₂, p' ≠ p := by
    by_contra! h
    apply singleton
    ext u
    rw [Finset.mem_singleton]
    constructor
    · exact h u
    · rintro rfl
      exact hp
  obtain ⟨p', hp', different⟩ := other
  have lineSingleton : L₁ ∩ L₂ = {l} := by
    ext v
    rw [Finset.mem_singleton]
    constructor
    · intro hv
      by_contra ne
      exact noRectangle p p' l v (Ne.symm different) (Ne.symm ne)
        ⟨commonIncident p hp l hl, commonIncident p hp v hv,
          commonIncident p' hp' l hl, commonIncident p' hp' v hv⟩
    · rintro rfl
      exact hl
  right
  refine ⟨l, lineSingleton, ?_⟩
  apply one_side_incident (fun l p => I p l) L₁ L₂ P₁ P₂
  · intro Y X hy₁ hy₂ hx₁ hx₂
    obtain ⟨p, hp, l, hl, hit⟩ := below X Y hx₁ hx₂ hy₁ hy₂
    exact ⟨l, hl, p, hp, hit⟩
  · exact (Finset.mem_inter.mp hl).1
  · exact (Finset.mem_inter.mp hl).2


lemma row_preserves_edges {α β : Type} [DecidableEq α] [DecidableEq β]
    (P₁ P₂ : Finset α) (L₁ L₂ K : Finset β) (p : α)
    (singleton : P₁ ∩ P₂ = {p}) (existing : K = L₁ ∨ K = L₂) :
    ∀ u v, u ∈ P₁ → u ∈ P₂ → v ∈ L₁ → v ∈ L₂ → u = p ∧ v ∈ K := by
  intro u v hu₁ hu₂ hv₁ hv₂
  constructor
  · apply Finset.mem_singleton.mp
    rw [← singleton]
    exact Finset.mem_inter.mpr ⟨hu₁, hu₂⟩
  · rcases existing with rfl | rfl
    · exact hv₁
    · exact hv₂

end PEqualNP.Outside.L_meta_2583.TwoRectangles

namespace PEqualNP.Outside.L_meta_2583.PlaneGeometry

def rectangleHits {N : Nat} (I : Fin N → Fin N → Prop) (p l : Fin N)
    (A B : Finset (Fin N)) : Prop :=
  (∃ a ∈ A, I a l) ∧ (∃ b ∈ B, I p b)

def hasIncidence {N : Nat} (I : Fin N → Fin N → Prop)
    (A B : Finset (Fin N)) : Prop := ∃ a ∈ A, ∃ b ∈ B, I a b

lemma rectangle_point_center {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p l : Fin N) (edge : I p l) (r : Fin N) :
    (∀ A B : Finset (Fin N), rectangleHits I p l A B → r ∈ A → hasIncidence I A B) ↔ r = p := by
  constructor
  · intro safe
    by_contra rp
    obtain ⟨m, hm, unique⟩ := hu p r (Ne.symm rp)
    have fresh : ∃ b : Fin N, I p b ∧ b ≠ l ∧ b ≠ m := by
      by_contra! no
      have sub : Finset.univ.filter (fun b => I p b) ⊆ ({l, m} : Finset (Fin N)) := by
        intro b hb
        have pb := (Finset.mem_filter.mp hb).2
        by_cases eq : b = l
        · simp [eq]
        · have eqm := no b pb eq
          simp [eqm]
      have bound := Finset.card_le_card sub
      rw [lines_through q N I (by omega) hN hl hu p] at bound
      have pair : ({l, m} : Finset (Fin N)).card ≤ 2 := by
        by_cases lm : l = m <;> simp [lm]
      omega
    obtain ⟨b, pb, bl, bm⟩ := fresh
    have rb : ¬ I r b := fun rb => bm (unique b ⟨pb, rb⟩)
    have ac : ((Finset.univ.filter (fun a => I a l)).erase p).card = q := by
      rw [Finset.card_erase_of_mem (by simp [edge]), hl l]
      rfl
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < ((Finset.univ.filter (fun a => I a l)).erase p).card by omega)
    have ap : a ≠ p := Finset.ne_of_mem_erase ha
    have al : I a l := (Finset.mem_filter.mp (Finset.mem_erase.mp ha).2).2
    have ab : ¬ I a b := fun ab => bl ((hu p a ap.symm).unique ⟨pb, ab⟩ ⟨edge, al⟩)
    have bad := safe {a, r} {b} ⟨⟨a, by simp, al⟩, ⟨b, by simp, pb⟩⟩ (by simp)
    obtain ⟨x, hx, y, hy, xy⟩ := bad
    simp only [Finset.mem_singleton] at hy
    subst y
    rcases Finset.mem_insert.mp hx with h | h
    · exact ab (h ▸ xy)
    · have xr := Finset.mem_singleton.mp h
      exact rb (xr ▸ xy)
  · intro equality A B hit hp
    subst r
    obtain ⟨b, hb, pb⟩ := hit.2
    exact ⟨p, hp, b, hb, pb⟩

lemma rectangle_line_center {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p l : Fin N) (edge : I p l) (r : Fin N) :
    (∀ A B : Finset (Fin N), rectangleHits I p l A B → r ∈ B → hasIncidence I A B) ↔ r = l := by
  have transpose := rectangle_point_center (fun x y => I y x) hq hN
    (lines_through q N I (by omega) hN hl hu)
    (fun x y ne => lines_intersect I (by omega) hN hl hu x y ne) l p edge r
  constructor
  · intro safe
    apply transpose.mp
    intro A B hit hr
    obtain ⟨a, ha, b, hb, ab⟩ := safe B A ⟨hit.2, hit.1⟩ hr
    exact ⟨b, hb, a, ha, ab⟩
  · intro equality A B hit hlB
    subst r
    obtain ⟨a, ha, al⟩ := hit.1
    exact ⟨a, ha, l, hlB, al⟩

lemma rectangle_selector_centers {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p l : Fin N) (edge : I p l) (P L : Finset (Fin N))
    (safe : ∀ A B : Finset (Fin N), rectangleHits I p l A B →
      ((A ∩ P).Nonempty ∨ (B ∩ L).Nonempty) → hasIncidence I A B) :
    P ⊆ {p} ∧ L ⊆ {l} := by
  constructor
  · intro r hr
    apply Finset.mem_singleton.mpr
    apply (rectangle_point_center I hq hN hl hu p l edge r).mp
    intro A B hit hA
    exact safe A B hit (Or.inl ⟨r, Finset.mem_inter.mpr ⟨hA, hr⟩⟩)
  · intro r hr
    apply Finset.mem_singleton.mpr
    apply (rectangle_line_center I hq hN hl hu p l edge r).mp
    intro A B hit hB
    exact safe A B hit (Or.inr ⟨r, Finset.mem_inter.mpr ⟨hB, hr⟩⟩)

end PEqualNP.Outside.L_meta_2583.PlaneGeometry


namespace PEqualNP.Outside.L_meta_2583.RectangleWitness

open scoped BigOperators

lemma point_avoiding (q N r : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hdegree : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (hr : r ≤ q) (centres : Fin r → Fin N) (l : Fin N) :
    ∃ p, I p l ∧ ∀ i, p ≠ centres i := by
  classical
  let T : Finset (Fin N) := Finset.univ.image centres
  have ht : T.card ≤ r := by
    exact Finset.card_image_le.trans (by simp)
  by_contra h
  push Not at h
  have hs : (Finset.univ.filter fun p => I p l) ⊆ T := by
    intro p hp
    obtain ⟨i, hi⟩ := h p (Finset.mem_filter.mp hp).2
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.symm⟩
  have hc := Finset.card_le_card hs
  rw [hdegree] at hc
  omega

lemma line_avoiding (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hdegree : ∀ p, (Finset.univ.filter fun l => I p l).card = q+1)
    (hunique : ∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l)
    (A : Finset (Fin N)) (ha : A.card ≤ q) (p : Fin N) (hp : p ∉ A) :
    ∃ l, I p l ∧ ∀ a ∈ A, ¬I a l := by
  classical
  let bad (a : Fin N) : Finset (Fin N) := Finset.univ.filter fun l => I p l ∧ I a l
  have hbad : ∀ a ∈ A, (bad a).card ≤ 1 := by
    intro a ha
    apply Finset.card_le_one.mpr
    intro l hl l' hl'
    have hpa : p ≠ a := by
      intro he
      subst a
      exact hp ha
    obtain ⟨k, hk, hu⟩ := hunique p a hpa
    exact (hu l (Finset.mem_filter.mp hl).2).trans (hu l' (Finset.mem_filter.mp hl').2).symm
  let B := A.biUnion bad
  have hB : B.card ≤ A.card := by
    calc
      B.card ≤ ∑ a ∈ A, (bad a).card := Finset.card_biUnion_le
      _ ≤ ∑ a ∈ A, 1 := Finset.sum_le_sum hbad
      _ = A.card := by simp
  by_contra h
  push Not at h
  have hs : (Finset.univ.filter fun l => I p l) ⊆ B := by
    intro l hl
    have hpl := (Finset.mem_filter.mp hl).2
    obtain ⟨a, ha, hal⟩ := h l hpl
    apply Finset.mem_biUnion.mpr
    exact ⟨a, ha, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl, hal⟩⟩
  have hc := Finset.card_le_card hs
  rw [hdegree] at hc
  omega

lemma rectangle_family_negative (q N r : ℕ)
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hline : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (hpoint : ∀ p, (Finset.univ.filter fun l => I p l).card = q+1)
    (hunique : ∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l)
    (hr : r ≤ q) (centres lines : Fin r → Fin N) :
    ∃ A B : Finset (Fin N), A.card ≤ r ∧ B.card ≤ r ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬I a b) ∧
      (∀ i, ∃ a ∈ A, I a (lines i)) ∧
      (∀ i, ∃ b ∈ B, I (centres i) b) := by
  classical
  have hx : ∀ i, ∃ a, I a (lines i) ∧ ∀ j, a ≠ centres j :=
    fun i => point_avoiding q N r I hline hr centres (lines i)
  choose a ha hne using hx
  let A : Finset (Fin N) := Finset.univ.image a
  have hA : A.card ≤ r := Finset.card_image_le.trans (by simp)
  have hcentres : ∀ i, centres i ∉ A := by
    intro i hi
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hi
    exact hne j i he
  have hy : ∀ i, ∃ b, I (centres i) b ∧ ∀ c ∈ A, ¬I c b :=
    fun i => line_avoiding q N I hpoint hunique A (hA.trans hr) (centres i) (hcentres i)
  choose b hb havoid using hy
  let B : Finset (Fin N) := Finset.univ.image b
  refine ⟨A, B, hA, Finset.card_image_le.trans (by simp), ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact havoid i x hx
  · intro i
    exact ⟨a i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ha i⟩
  · intro i
    exact ⟨b i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hb i⟩

lemma rectangle_family_false_positive (q N r : ℕ)
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hline : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (hpoint : ∀ p, (Finset.univ.filter fun l => I p l).card = q+1)
    (hunique : ∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l)
    (hr : r ≤ q) (centres lines : Fin r → Fin N) :
    ∃ z : Fin (N+N) → Bool,
      (¬∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      ∀ i, (∃ p, I p (lines i) ∧ z (Fin.castAdd N p) = true) ∧
        (∃ l, I (centres i) l ∧ z (Fin.natAdd N l) = true) := by
  classical
  obtain ⟨A, B, hA, hB, hind, ha, hb⟩ :=
    rectangle_family_negative q N r I hline hpoint hunique hr centres lines
  let z : Fin (N+N) → Bool :=
    Fin.addCases (fun p => decide (p ∈ A)) (fun l => decide (l ∈ B))
  have hzP (p : Fin N) : z (Fin.castAdd N p) = decide (p ∈ A) := by simp [z]
  have hzL (l : Fin N) : z (Fin.natAdd N l) = decide (l ∈ B) := by
    exact Fin.addCases_right l
  refine ⟨z, ?_, ?_⟩
  · rintro ⟨p, l, hpl, hp, hl⟩
    rw [hzP] at hp
    rw [hzL] at hl
    exact hind p (of_decide_eq_true hp) l (of_decide_eq_true hl) hpl
  · intro i
    obtain ⟨p, hp, hpi⟩ := ha i
    obtain ⟨l, hl, hil⟩ := hb i
    refine ⟨⟨p, hpi, ?_⟩, ⟨l, hil, ?_⟩⟩
    · simpa only [hzP, decide_eq_true_eq] using hp
    · simpa only [hzL, decide_eq_true_eq] using hl

end PEqualNP.Outside.L_meta_2583.RectangleWitness

namespace PEqualNP.Outside.L_meta_2583.RectangleFamilies

variable {n m : Nat} {ι κ : Type}
variable (I : Fin n → Fin m → Prop) [DecidableRel I]
variable (P : ι → Finset (Fin n)) (L : κ → Finset (Fin m))

def HitsPointClauses (X : Finset (Fin n)) : Prop := ∀ i, ∃ p ∈ X, p ∈ P i

def HitsLineClauses (Y : Finset (Fin m)) : Prop := ∀ j, ∃ l ∈ Y, l ∈ L j

def BelowIncidence : Prop := ∀ X Y,
  HitsPointClauses P X → HitsLineClauses L Y → ∃ p ∈ X, ∃ l ∈ Y, I p l

lemma point_clause (below : BelowIncidence I P L) (p : Fin n) (common : ∀ i, p ∈ P i) :
    ∃ j, ∀ l ∈ L j, I p l := by
  classical
  by_contra! no
  let Y := Finset.univ.filter (fun l => ¬ I p l)
  have points : HitsPointClauses P {p} := fun i => ⟨p, by simp, common i⟩
  have lines : HitsLineClauses L Y := by
    intro j
    obtain ⟨l, hl, bad⟩ := no j
    exact ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, bad⟩, hl⟩
  obtain ⟨r, hr, l, hl, edge⟩ := below {p} Y points lines
  have rp := Finset.mem_singleton.mp hr
  subst r
  exact (Finset.mem_filter.mp hl).2 edge

lemma line_clause (below : BelowIncidence I P L) (l : Fin m) (common : ∀ j, l ∈ L j) :
    ∃ i, ∀ p ∈ P i, I p l := by
  have transposed : BelowIncidence (fun l p => I p l) L P := by
    intro Y X lineHit pointHit
    obtain ⟨p, hp, l, hl, edge⟩ := below X Y pointHit lineHit
    exact ⟨l, hl, p, hp, edge⟩
  exact point_clause (fun l p => I p l) L P transposed l common

lemma common_cross (below : BelowIncidence I P L) (p : Fin n) (l : Fin m)
    (point : ∀ i, p ∈ P i) (line : ∀ j, l ∈ L j) : I p l := by
  obtain ⟨j, hj⟩ := point_clause I P L below p point
  exact hj l (line j)

lemma star_envelope
    (noFour : ∀ p p' : Fin n, ∀ l l' : Fin m, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (below : BelowIncidence I P L)
    (useful : ∃ p : Fin n, ∃ l : Fin m, (∀ i, p ∈ P i) ∧ (∀ j, l ∈ L j)) :
    (∃ p : Fin n, ∃ j : κ,
      (∀ p' : Fin n, (∀ i, p' ∈ P i) → p' = p) ∧ (∀ l ∈ L j, I p l)) ∨
    (∃ l : Fin m, ∃ i : ι,
      (∀ l' : Fin m, (∀ j, l' ∈ L j) → l' = l) ∧ (∀ p ∈ P i, I p l)) := by
  classical
  obtain ⟨p, l, hp, hl⟩ := useful
  by_cases singleton : ∀ p' : Fin n, (∀ i, p' ∈ P i) → p' = p
  · obtain ⟨j, hj⟩ := point_clause I P L below p hp
    exact Or.inl ⟨p, j, singleton, hj⟩
  · push_neg at singleton
    obtain ⟨p', hp', diff⟩ := singleton
    have singleLine : ∀ l' : Fin m, (∀ j, l' ∈ L j) → l' = l := by
      intro l' hl'
      by_contra different
      exact noFour p p' l l' (Ne.symm diff) (Ne.symm different)
        ⟨common_cross I P L below p l hp hl,
          common_cross I P L below p l' hp hl',
          common_cross I P L below p' l hp' hl,
          common_cross I P L below p' l' hp' hl'⟩
    obtain ⟨i, hi⟩ := line_clause I P L below l hl
    exact Or.inr ⟨l, i, singleLine, hi⟩

lemma point_envelope_preserves (p : Fin n) (j : κ)
    (singleton : ∀ p' : Fin n, (∀ i, p' ∈ P i) → p' = p) :
    ∀ p' : Fin n, ∀ l : Fin m, (∀ i, p' ∈ P i) → (∀ j, l ∈ L j) → p' = p ∧ l ∈ L j := by
  intro p' l hp hl
  exact ⟨singleton p' hp, hl j⟩

lemma line_envelope_preserves (l : Fin m) (i : ι)
    (singleton : ∀ l' : Fin m, (∀ j, l' ∈ L j) → l' = l) :
    ∀ p : Fin n, ∀ l' : Fin m, (∀ i, p ∈ P i) → (∀ j, l' ∈ L j) → l' = l ∧ p ∈ P i := by
  intro p l' hp hl
  exact ⟨singleton l' hl, hp i⟩

end PEqualNP.Outside.L_meta_2583.RectangleFamilies
