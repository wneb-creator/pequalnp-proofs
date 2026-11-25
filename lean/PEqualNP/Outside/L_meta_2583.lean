import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux

namespace SingleLevel

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadK PEqualNP.TopForm PEqualNP.EdgeOwnership

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
  rfl

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
  rfl

lemma s2230_leaf_eq (a b w : ℕ) :
    leafVectors [a, b] 1 w =
      if w ∈ [a, b] then [[if a = w then 1 else 0, if b = w then 1 else 0]] else [] := by
  rfl


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


lemma foldl_coneStep_length (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_coneStep_prefix (n : ℕ) (gs : List Gate) (acc : List (List ℕ))
    (j : ℕ) (hj : j < acc.length) :
    (gs.foldl (coneStep n) acc).getD j [] = acc.getD j [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hj' : j < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (coneStep n acc g) hj']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [coneStep, List.getElem?_append_left hj]

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take j).foldl (coneStep n) [] with hacc
  have hacc_len : acc.length = j := by
    rw [hacc, foldl_coneStep_length, List.length_nil, List.length_take]
    omega
  have hpref : ∀ k < j, (cones n C).getD k [] = acc.getD k [] := by
    intro k hk
    unfold cones
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_coneStep_prefix n (C.gates.drop j) acc k (by omega)
  have hstep : (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: acc.getD (w - n) []) := by
    unfold cones
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : j < (coneStep n acc C.gates[j]).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_coneStep_prefix n (C.gates.drop (j + 1)) (coneStep n acc C.gates[j]) j hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [coneStep, List.getElem?_append_right (by omega : acc.length ≤ j),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      s2230_gateAt_eq C j hj]
  unfold InCone
  rw [hstep, List.mem_flatMap]
  constructor
  · rintro ⟨w, hw, hi⟩
    rw [List.mem_filter] at hw
    have hbounds : n ≤ w ∧ w < n + j := by simpa using hw.2
    rw [List.mem_cons] at hi
    refine ⟨w, hw.1, hbounds.1, hbounds.2, ?_⟩
    rcases hi with rfl | hi
    · exact Or.inl rfl
    · right
      rw [hpref (w - n) (by omega)]
      exact hi
  · rintro ⟨w, hw, hnw, hlt, hi⟩
    refine ⟨w, ?_, ?_⟩
    · rw [List.mem_filter]
      exact ⟨hw, by simpa using And.intro hnw hlt⟩
    · rw [List.mem_cons]
      rcases hi with rfl | hi
      · exact Or.inl rfl
      · right
        rw [← hpref (w - n) (by omega)]
        exact hi

inductive Pure (n : ℕ) (C : Circuit) : ℕ → Prop where
  | input {w} : w < n → Pure n C w
  | disj {j} : j < C.size → (gateAt C j).op = GateOp.or →
      (∀ w ∈ (gateAt C j).inputs, Pure n C w) → Pure n C (n + j)

lemma value_gate_clean {n : ℕ} {C : Circuit} (hC : IsAO2 n C)
    (x : Fin n → Bool) (j : ℕ) (hj : j < C.size) :
    s2230_W n C x (n + j) = (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i => s2230_W n C x i) := by
  rw [s2230_W_gate n C x j hj]
  congr 1
  exact List.map_congr_left fun i hi => ite_eq_left (hC.2.1 j hj i hi)

lemma or_vector {n : ℕ} {C : Circuit} (hC : IsAO2 n C)
    (S : List ℕ) (j : ℕ) (hj : j < C.size) (ho : (gateAt C j).op = GateOp.or)
    (i : ℕ) (hi : i ∈ (gateAt C j).inputs)
    (v : List ℕ) (hv : v ∈ s2230_RV C n S 1 i) :
    v ∈ s2230_RV C n S 1 (n + j) := by
  obtain ⟨Rp, hRp, hRV⟩ := s2230_RV_gate C n S 1 j hj
  rw [hRV, s2230_FR_or _ _ _ _ ho]
  apply mem_orFold
  refine Or.inr ⟨Rp.getD i [], List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩
  rw [hRp i (hC.2.1 j hj i hi)]
  exact hv

lemma pure_unit {n : ℕ} {C : Circuit} (hC : IsAO2 n C)
    (S : Finset (Fin n)) {w : ℕ} (pure : Pure n C w)
    (hw : s2230_W n C (setInput S) w = true) :
    ∃ i : Fin n, uv (setList S) i.val ∈ s2230_RV C n (setList S) 1 w ∧
      s2230_W n C (setInput {i}) w = true := by
  induction pure with
  | @input w hlt =>
    have hs : (⟨w, hlt⟩ : Fin n) ∈ S := by
      rw [s2230_W_input n C _ w hlt] at hw
      simpa [setInput] using hw
    refine ⟨⟨w, hlt⟩, ?_, ?_⟩
    · rw [s2230_RV_input C n (setList S) 1 w hlt]
      simp only [leafVectors, ite_eq_left (mem_setList S w hlt hs), uv]
      exact List.mem_singleton_self _
    · rw [s2230_W_input n C _ w hlt]
      simp [setInput]
  | @disj j hj ho children ih =>
    rw [value_gate_clean hC _ j hj, ho] at hw
    obtain ⟨w, hw, ht⟩ : ∃ w ∈ (gateAt C j).inputs,
        s2230_W n C (setInput S) w = true := by simpa [GateOp.eval] using hw
    obtain ⟨i, hi, hs⟩ := ih w hw ht
    refine ⟨i, or_vector hC _ j hj ho w hw _ hi, ?_⟩
    rw [value_gate_clean hC _ j hj, ho]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    exact ⟨true, ⟨w, hw, hs⟩, rfl⟩

lemma pure_of_no_and {n : ℕ} {C : Circuit} (hC : IsAO2 n C) (w : ℕ)
    (bound : w < n + C.size)
    (free : ∀ i < C.size, (gateAt C i).op = GateOp.and →
      w ≠ n + i ∧ (n ≤ w → ¬ InCone n C i (w - n))) : Pure n C w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hinput : w < n
    · exact Pure.input hinput
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.size := by omega
    have hop : (gateAt C j).op = GateOp.or := by
      rcases hC.1 (gateAt C j) (by rw [s2230_gateAt_eq C j hj]; exact List.getElem_mem hj) with ha | ho
      · exact ((free j hj ha).1 rfl).elim
      · exact ho
    apply Pure.disj hj hop
    intro v hv
    have hvlt := hC.2.1 j hj v hv
    apply ih v hvlt (by omega)
    intro i hi ha
    have hnot : ¬ InCone n C i j := by simpa using (free i hi ha).2 (by omega)
    constructor
    · intro eq
      apply hnot
      apply (inCone_iff n C i j hj).mpr
      refine ⟨v, hv, by omega, hvlt, Or.inl ?_⟩
      omega
    · intro hn hvcone
      apply hnot
      exact (inCone_iff n C i j hj).mpr ⟨v, hv, hn, hvlt, Or.inr hvcone⟩

lemma and_inputs_pure {n : ℕ} {C : Circuit} (hC : IsAO2 n C)
    (single : ∀ i < C.size, ∀ j < C.size,
      (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and → ¬ InCone n C i j)
    (j : ℕ) (hj : j < C.size) (ha : (gateAt C j).op = GateOp.and)
    (w : ℕ) (hw : w ∈ (gateAt C j).inputs) : Pure n C w := by
  have hlt := hC.2.1 j hj w hw
  apply pure_of_no_and hC w (by omega)
  intro i hi hai
  constructor
  · intro eq
    apply single i hi j hj hai ha
    apply (inCone_iff n C i j hj).mpr
    exact ⟨w, hw, by omega, hlt, Or.inl (by omega)⟩
  · intro hn hc
    exact single i hi j hj hai ha ((inCone_iff n C i j hj).mpr ⟨w, hw, hn, hlt, Or.inr hc⟩)

lemma single_level_vectors {n : ℕ} {C : Circuit} (hC : IsAO2 n C)
    (single : ∀ i < C.size, ∀ j < C.size,
      (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and → ¬ InCone n C i j)
    (noSingleton : ∀ j < C.size, (gateAt C j).op = GateOp.and →
      ∀ i : Fin n, s2230_W n C (setInput {i}) (n + j) = false)
    (S : Finset (Fin n)) (w : ℕ) (hw : s2230_W n C (setInput S) w = true) :
    ∃ v ∈ s2230_RV C n (setList S) 1 w, ∀ a ∈ v, a ≤ 1 := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · obtain ⟨i, hi, _⟩ := pure_unit hC S (Pure.input hwn) hw
      refine ⟨uv (setList S) i.val, hi, ?_⟩
      intro a ha
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
      split_ifs <;> omega
    · by_cases hwl : w < n + C.size
      swap
      · have hf : s2230_W n C (setInput S) w = false := by
          exact s2230_getD_ge_length _ _ (by rw [s2230_wires_length]; change n + C.size ≤ w; omega)
        rw [hf] at hw
        cases hw
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.size := by omega
      have back := hC.2.1 j hj
      have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or :=
        hC.1 (gateAt C j) (by rw [s2230_gateAt_eq C j hj]; exact List.getElem_mem hj)
      rcases hop with ha | ho
      · obtain ⟨a, b, inputs⟩ := List.length_eq_two.mp
          (hC.2.2 (gateAt C j) (by rw [s2230_gateAt_eq C j hj]; exact List.getElem_mem hj))
        have amem : a ∈ (gateAt C j).inputs := by simp [inputs]
        have bmem : b ∈ (gateAt C j).inputs := by simp [inputs]
        have hab : s2230_W n C (setInput S) a = true ∧ s2230_W n C (setInput S) b = true := by
          rw [value_gate_clean hC _ j hj, ha, inputs] at hw
          simpa [GateOp.eval] using hw
        obtain ⟨ia, hia, hsa⟩ := pure_unit hC S (and_inputs_pure hC single j hj ha a amem) hab.1
        obtain ⟨ib, hib, hsb⟩ := pure_unit hC S (and_inputs_pure hC single j hj ha b bmem) hab.2
        have distinct : ia.val ≠ ib.val := by
          intro same
          have eq : ia = ib := Fin.ext same
          subst ib
          have hn := noSingleton j hj ha ia
          rw [value_gate_clean hC _ j hj, ha, inputs] at hn
          simp [GateOp.eval, hsa, hsb] at hn
        obtain ⟨Rp, hRp, hRV⟩ := s2230_RV_gate C n (setList S) 1 j hj
        refine ⟨capAdd 1 (capAdd 1 ((setList S).map fun _ => 0) (uv (setList S) ia.val))
          (uv (setList S) ib.val), ?_, ?_⟩
        · rw [hRV, s2230_FR_and _ _ _ _ ha, inputs]
          simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
          rw [hRp a (back a amem), hRp b (back b bmem)]
          exact mem_andStep_of _ _ _ _ _
            (mem_andStep_of _ _ _ _ _ (List.mem_singleton_self _) hia) hib
        · intro e he
          unfold uv at he
          rw [capAdd_map, capAdd_map] at he
          obtain ⟨t, _, rfl⟩ := List.mem_map.mp he
          split_ifs <;> omega
      · rw [value_gate_clean hC _ j hj, ho] at hw
        obtain ⟨i, hi, ht⟩ : ∃ i ∈ (gateAt C j).inputs,
            s2230_W n C (setInput S) i = true := by simpa [GateOp.eval] using hw
        obtain ⟨v, hv, bound⟩ := ih i (back i hi) ht
        exact ⟨v, or_vector hC _ j hj ho i hi v hv, bound⟩

theorem single_level_read_one {n : ℕ} {C : Circuit} (hC : IsAO2 n C)
    (single : ∀ i < C.size, ∀ j < C.size,
      (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and → ¬ InCone n C i j)
    (noSingleton : ∀ j < C.size, (gateAt C j).op = GateOp.and →
      ∀ i : Fin n, s2230_W n C (setInput {i}) (n + j) = false) : IsReadK n C 1 := by
  intro S hS
  obtain ⟨v, hv, bound⟩ := single_level_vectors hC single noSingleton S C.output hS.1
  apply List.any_eq_true.mpr
  refine ⟨v, hv, List.all_eq_true.mpr ?_⟩
  intro a ha
  exact decide_eq_true (bound a ha)

theorem top_form_junk_empty_read_one {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsAO2 n C) (top : TopForm G C)
    (empty : junk G C = ∅) : IsReadK n C 1 := by
  have below : ∀ j < C.size, (gateAt C j).op = GateOp.and → BelowF G C j := by
    intro j hj ha x hx
    by_contra hf
    have bad : j ∈ junk G C := by
      simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range]
      refine ⟨hj, ha, hj, x, hx, ?_⟩
      cases e : graphFun G ∅ x <;> simp_all
    rw [empty] at bad
    exact Finset.notMem_empty j bad
  apply single_level_read_one hC
  · intro i hi j hj hai haj
    exact top i hi j hj hai (below i hi hai) haj
  · intro j hj ha i
    cases e : s2230_W n C (setInput {i}) (n + j)
    · rfl
    · have hf := below j hj ha (setInput {i}) e
      simp [graphFun, setInput] at hf

end SingleLevel

namespace PrimeReplacement

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Wire monotonicity infrastructure adapted from the checked L_meta_610 proof.
def wiresStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wiresStep_length (gs : List Gate) (w : List Bool) :
    (gs.foldl wiresStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wiresStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wiresStep_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) :
    (gs.foldl wiresStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (wiresStep w g).length := by
      simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (wiresStep w g) hlt]
    simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma getD_append_last_eq (w : List Bool) (b : Bool) (m : ℕ) (hm : w.length = m) :
    (w ++ [b]).getD m false = b := by
  subst hm
  simp [List.getD_eq_getElem?_getD]

lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma monotone_foldl_wiresStep (gs : List Gate)
    (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (w1 w2 : List Bool) (hlen : w1.length = w2.length)
    (hle : ∀ k : ℕ, w1.getD k false = true → w2.getD k false = true) :
    ∀ k : ℕ, (gs.foldl wiresStep w1).getD k false = true →
      (gs.foldl wiresStep w2).getD k false = true := by
  induction gs generalizing w1 w2 with
  | nil => exact hle
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := by
      simpa using hM g List.mem_cons_self
    have hM' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
      fun g' hg' => hM g' (List.mem_cons_of_mem g hg')
    apply ih hM' (wiresStep w1 g) (wiresStep w2 g)
    · simp only [wiresStep, List.length_append, List.length_cons, List.length_nil, hlen]
    · intro k hk
      by_cases hlt : k < w1.length
      · have hlt2 : k < w2.length := hlen ▸ hlt
        simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hk
        simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
        exact hle k hk
      · by_cases heq : k = w1.length
        · subst heq
          have hk1 : g.op.eval (g.inputs.map fun i => w1.getD i false) = true := by
            simpa [wiresStep, getD_append_last_eq w1 _ w1.length rfl] using hk
          rw [wiresStep, getD_append_last_eq w2 _ w1.length hlen.symm]
          rcases hg with hand | hor
          · rw [hand] at hk1 ⊢
            simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq,
              forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hk1 ⊢
            intro i hi
            exact hle i (hk1 i hi)
          · rw [hor] at hk1 ⊢
            simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hk1 ⊢
            obtain ⟨b, ⟨i, hi, rfl⟩, hbi⟩ := hk1
            exact ⟨true, ⟨i, hi, hle i hbi⟩, rfl⟩
        · have hge : (wiresStep w1 g).length ≤ k := by
            simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
            omega
          rw [getD_ge_length _ k hge] at hk
          cases hk


lemma getD_snoc_ne (w : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases hlt : i < w.length
  · exact List.getD_append _ _ _ _ hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma append_signal_le (w v : List Bool) (a b : Bool) (hlen : w.length = v.length)
    (h : ∀ i, w.getD i false = true → v.getD i false = true)
    (hab : a = true → b = true) :
    ∀ i, (w ++ [a]).getD i false = true → (v ++ [b]).getD i false = true := by
  intro i hi
  by_cases he : i = w.length
  · subst i
    rw [getD_append_last_eq w a _ rfl] at hi
    rw [getD_append_last_eq v b _ hlen.symm]
    exact hab hi
  · rw [getD_snoc_ne _ _ _ he] at hi
    rw [getD_snoc_ne _ _ _ (by omega)]
    exact h i hi

def MonoFn {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

def edgeInput {n : ℕ} (e : Fin n × Fin n) : Fin n → Bool :=
  fun i => decide (i = e.1 ∨ i = e.2)

def edgeValue {n : ℕ} (E : Finset (Fin n × Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ e ∈ E, x e.1 = true ∧ x e.2 = true)

lemma edgeInput_le {n : ℕ} (e : Fin n × Fin n) (x : Fin n → Bool)
    (ha : x e.1 = true) (hb : x e.2 = true) :
    ∀ i, edgeInput e i = true → x i = true := by
  intro i hi
  have h : i = e.1 ∨ i = e.2 := of_decide_eq_true hi
  rcases h with rfl | rfl
  · exact ha
  · exact hb

lemma edgeValue_pair {n : ℕ} (E : Finset (Fin n × Fin n)) (e : Fin n × Fin n)
    (he : e ∈ E) : edgeValue E (edgeInput e) = true := by
  apply decide_eq_true
  exact ⟨e, he, by simp [edgeInput], by simp [edgeInput]⟩

lemma lowered_eq_on_edges {n : ℕ} (E : Finset (Fin n × Fin n))
    (f : (Fin n → Bool) → Bool) (mono : MonoFn f)
    (below : ∀ x, f x = true → edgeValue E x = true)
    (edges : ∀ e ∈ E, f (edgeInput e) = true) :
    ∀ x, f x = edgeValue E x := by
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact below x
  · intro hx
    obtain ⟨e, he, ha, hb⟩ := of_decide_eq_true hx
    exact mono (edgeInput e) x (edgeInput_le e x ha hb) (edges e he)

lemma input_list_le {n : ℕ} (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) :
    ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
  intro i hi
  by_cases hil : i < n
  · rw [getD_ofFn x i hil] at hi
    rw [getD_ofFn y i hil]
    exact h ⟨i, hil⟩ hi
  · rw [getD_ge_length _ _ (by simp; omega)] at hi
    cases hi

def replacedValue {n : ℕ} (A B : List Gate) (r : (Fin n → Bool) → Bool) (o : ℕ)
    (x : Fin n → Bool) : Bool :=
  (B.foldl wiresStep (A.foldl wiresStep (List.ofFn x) ++ [r x])).getD o false

lemma replaced_mono {n : ℕ} (A B : List Gate)
    (hA : ∀ g ∈ A, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hB : ∀ g ∈ B, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (r : (Fin n → Bool) → Bool) (hr : MonoFn r) (o : ℕ) :
    MonoFn (replacedValue A B r o) := by
  intro x y hxy
  apply monotone_foldl_wiresStep B hB _ _
    (by simp [foldl_wiresStep_length])
  apply append_signal_le _ _ _ _ (by simp [foldl_wiresStep_length])
  · exact monotone_foldl_wiresStep A hA _ _ (by simp) (input_list_le x y hxy)
  · exact hr x y hxy

-- A lower monotone replacement that agrees on every accepted edge preserves the whole function.
theorem lower_wire_preserves {n : ℕ} (E : Finset (Fin n × Fin n))
    (A B : List Gate) (g : Gate) (o : ℕ)
    (hA : ∀ t ∈ A, t.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hB : ∀ t ∈ B, t.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (r : (Fin n → Bool) → Bool) (hr : MonoFn r)
    (below : ∀ x, r x = true →
      g.op.eval (g.inputs.map fun i => (A.foldl wiresStep (List.ofFn x)).getD i false) = true)
    (same : ∀ e ∈ E, r (edgeInput e) =
      g.op.eval (g.inputs.map fun i => (A.foldl wiresStep (List.ofFn (edgeInput e))).getD i false))
    (computes : ∀ x : Fin n → Bool, Circuit.eval ⟨A ++ g :: B, o⟩ (List.ofFn x) = edgeValue E x) :
    ∀ x, replacedValue A B r o x = edgeValue E x := by
  apply lowered_eq_on_edges E _ (replaced_mono A B hA hB r hr o)
  · intro x hx
    have hle := monotone_foldl_wiresStep B hB
      (A.foldl wiresStep (List.ofFn x) ++ [r x])
      (wiresStep (A.foldl wiresStep (List.ofFn x)) g)
      (by simp [wiresStep])
      (append_signal_le _ _ _ _ rfl (fun _ h => h) (below x)) o hx
    have horig : (B.foldl wiresStep (wiresStep (A.foldl wiresStep (List.ofFn x)) g)).getD o false
        = Circuit.eval ⟨A ++ g :: B, o⟩ (List.ofFn x) := by
      simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
      rfl
    rw [horig, computes x] at hle
    exact hle
  · intro e he
    rw [replacedValue, same e he]
    have horig :
        (B.foldl wiresStep (A.foldl wiresStep (List.ofFn (edgeInput e)) ++
          [g.op.eval (g.inputs.map fun i => (A.foldl wiresStep (List.ofFn (edgeInput e))).getD i false)])).getD o false
          = Circuit.eval ⟨A ++ g :: B, o⟩ (List.ofFn (edgeInput e)) := by
      simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
      rfl
    rw [horig, computes]
    exact edgeValue_pair E e he

end PrimeReplacement

namespace FanoFinite

def fanoPairs : List (Nat × Nat) :=
  [(1,0), (3,0), (5,0), (0,1), (3,1), (4,1), (2,2), (3,2), (6,2),
   (0,3), (1,3), (2,3), (1,4), (4,4), (6,4), (0,5), (5,5), (6,5),
   (2,6), (4,6), (5,6)]

def fanoInc (p l : Fin 7) : Prop := (p.val, l.val) ∈ fanoPairs

instance fanoIncDecidable : DecidableRel fanoInc := fun p l =>
  inferInstanceAs (Decidable ((p.val, l.val) ∈ fanoPairs))

theorem fano_line_size :
    ∀ l : Fin 7, (Finset.univ.filter (fun p => fanoInc p l)).card = 3 := by
  decide +kernel

theorem fano_point_pair :
    ∀ p p' : Fin 7, p ≠ p' → ∃! l : Fin 7, fanoInc p l ∧ fanoInc p' l := by
  unfold ExistsUnique
  decide +kernel

def fanoFunction (z : Fin 14 → Bool) : Bool :=
  decide (∃ p l : Fin 7, fanoInc p l ∧ z (Fin.castAdd 7 p) = true ∧
    z (Fin.natAdd 7 l) = true)

def maskInput (r : Nat) (i : Fin 14) : Bool := r.testBit i.val

def maximalFalseMasks : List Nat :=
  [127, 213, 358, 452, 563, 657, 802, 1144, 1232, 1376, 1584, 2093,
   2181, 2340, 2593, 3112, 3872, 4126, 4244, 4358, 4626, 5144, 5776,
   6156, 6532, 8267, 8385, 8514, 8707, 9288, 9664, 10249, 10881,
   12298, 13058, 15368, 16256]

theorem maximalFalseMasks_length : maximalFalseMasks.length = 37 := rfl

theorem listed_masks_false :
    ∀ r ∈ maximalFalseMasks, fanoFunction (maskInput r) = false := by
  decide +kernel

theorem listed_masks_maximal :
    ∀ r ∈ maximalFalseMasks, ∀ i : Fin 14, maskInput r i = false →
      fanoFunction (fun j => if j = i then true else maskInput r j) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem point_boundary_cover :
    ∀ x : Fin 7 → Bool, ∃ m ∈ maximalFalseMasks,
      (∀ p : Fin 7, x p = true → maskInput m (Fin.castAdd 7 p) = true) ∧
      (∀ l : Fin 7, (∀ p : Fin 7, fanoInc p l → x p = false) →
        maskInput m (Fin.natAdd 7 l) = true) := by
  decide +kernel

theorem false_boundary_complete (z : Fin 14 → Bool)
    (hz : fanoFunction z = false) :
    ∃ m ∈ maximalFalseMasks, ∀ i : Fin 14,
      z i = true → maskInput m i = true := by
  obtain ⟨m, hm, hp, hl⟩ := point_boundary_cover (fun p => z (Fin.castAdd 7 p))
  refine ⟨m, hm, ?_⟩
  intro i
  refine Fin.addCases (m := 7) (n := 7)
    (motive := fun i => z i = true → maskInput m i = true) ?_ ?_ i
  · exact hp
  · intro l hzline
    apply hl l
    intro p hinc
    cases hpoint : z (Fin.castAdd 7 p) with
    | false => rfl
    | true =>
      have ht : fanoFunction z = true := by
        unfold fanoFunction
        simp only [decide_eq_true_eq]
        exact ⟨p, l, hinc, hpoint, hzline⟩
      rw [hz] at ht
      contradiction

def edgeInput (p l : Fin 7) (i : Fin 14) : Bool :=
  decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)

theorem edgeInput_true (p l : Fin 7) (hinc : fanoInc p l) :
    fanoFunction (edgeInput p l) = true := by
  unfold fanoFunction
  simp only [decide_eq_true_eq]
  refine ⟨p, l, hinc, ?_, ?_⟩ <;> simp [edgeInput]

theorem true_boundary_complete (z : Fin 14 → Bool)
    (hz : fanoFunction z = true) :
    ∃ p l : Fin 7, fanoInc p l ∧
      ∀ i : Fin 14, edgeInput p l i = true → z i = true := by
  unfold fanoFunction at hz
  simp only [decide_eq_true_eq] at hz
  obtain ⟨p, l, hinc, hp, hl⟩ := hz
  refine ⟨p, l, hinc, ?_⟩
  intro i hi
  simp only [edgeInput, decide_eq_true_eq] at hi
  rcases hi with rfl | rfl
  · exact hp
  · exact hl

end FanoFinite

lemma incidence_card (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun e => I e.1 e.2)).card = N * (q + 1) := by
  have hc : ((Finset.univ : Finset (Fin N × Fin N)).filter (fun e => I e.1 e.2)).card =
      ∑ l : Fin N, (Finset.univ.filter (fun p => I p l)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_comm]
  rw [hc]
  simp [hl]

lemma eq_of_minimal_true_maximal_false {α : Type*} [Preorder α] [Finite α]
    (f g : α → Bool) (hg : Monotone g)
    (hp : ∀ x, Minimal (fun y => f y = true) x → g x = true)
    (hn : ∀ x, Maximal (fun y => f y = false) x → g x = false) : f = g := by
  classical
  funext x
  cases hx : f x with
  | false =>
    obtain ⟨y, hxy, hy⟩ := (Set.toFinite {y | f y = false}).exists_le_maximal hx
    have hm := hg hxy
    have hh := hn y hy
    cases hgx : g x <;> simp_all
    exact (by decide : ¬ (true : Bool) ≤ false) hm
  | true =>
    obtain ⟨y, hyx, hy⟩ := (Set.toFinite {y : OrderDual α | f y = true}).exists_le_maximal hx
    have hm := hg hyx
    have hh := hp y hy
    cases hgx : g x <;> simp_all
    exact (by decide : ¬ (true : Bool) ≤ false) hm

end PEqualNP.Outside.L_meta_2583_aux
