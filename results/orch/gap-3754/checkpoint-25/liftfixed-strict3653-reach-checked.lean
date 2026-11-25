import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3754.Strict3653

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.SplitCount PEqualNP.ReadTwo

lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w gt => w ++ [gt.op.eval (gt.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons gt rest ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w gt => w ++ [gt.op.eval (gt.inputs.map fun idx => w.getD idx false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons gt rest ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [gt.op.eval (gt.inputs.map fun idx => acc.getD idx false)]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [ih _ hlt]
    simp [List.getD, List.getElem?_append_left hi]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  exact foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlen : i < (List.ofFn x).length := by simpa using hi
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlen]
  simp [List.getD, hi]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 (gateAt C j) (gateAt_mem hj)
  unfold opnd
  cases hl : (gateAt C j).inputs with
  | nil => simp [hl] at hlen
  | cons a l =>
    cases l with
    | nil => simp [hl] at hlen
    | cons b l' =>
      cases l' with
      | nil => simp [hl]
      | cons c l'' => simp [hl] at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj (opnd C j b) (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    have hg : gateAt C j = C.gates[j] := by
      unfold gateAt
      exact List.getD_eq_getElem _ _ hj
    rw [hg]
    simpa using (List.take_append_drop j C.gates).symm.trans (by
      congr 1
      exact (List.cons_getElem_drop_succ (h := hj)).symm)
  set step : List Bool → Gate → List Bool :=
    fun w gt => w ++ [gt.op.eval (gt.inputs.map fun i => w.getD i false)]
  set pre := (C.gates.take j).foldl step (List.ofFn x)
  have hpre_len : pre.length = n + j := by
    have h1 := foldl_wires_len (C.gates.take j) (List.ofFn x)
    simp only [List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at h1
    exact h1
  have h_eq : C.gates.foldl step (List.ofFn x) =
      (C.gates.drop (j + 1)).foldl step (step pre (gateAt C j)) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have h_pre_get : ∀ i < n + j, (C.gates.foldl step (List.ofFn x)).getD i false = pre.getD i false := by
    intro i hi
    rw [h_eq]
    have hi1 : i < (step pre (gateAt C j)).length := by
      simp only [step, List.length_append, List.length_singleton, hpre_len]
      omega
    rw [foldl_wires_getD_lt _ _ i hi1]
    simp only [step]
    have hi2 : i < pre.length := by omega
    simp [List.getD, List.getElem?_append_left hi2]
  have h_nj : (C.gates.foldl step (List.ofFn x)).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => pre.getD i false) := by
    rw [h_eq]
    have hlt : n + j < (step pre (gateAt C j)).length := by
      simp only [step, List.length_append, List.length_singleton, hpre_len]
      omega
    rw [foldl_wires_getD_lt _ _ (n + j) hlt]
    simp only [step]
    have hle : pre.length ≤ n + j := by omega
    simp [List.getD, List.getElem?_append_right hle, hpre_len]
  rw [h_nj, gate_inputs_eq hAO hj]
  have h0 := h_pre_get (opnd C j 0) (opnd_lt hAO hj 0)
  have h1 := h_pre_get (opnd C j 1) (opnd_lt hAO hj 1)
  simp only [List.map_cons, List.map_nil, ← h0, ← h1]

lemma wval_gate_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wval C x (n + j) = (wval C x (opnd C j 0) && wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]
  simp [GateOp.eval]

lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]
  simp [GateOp.eval]

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  have hlen : (C.wires (List.ofFn x)).length ≤ w := by
    rw [wires_length, List.length_ofFn]
    exact hw
  exact List.getD_eq_default _ _ hlen

lemma wval_allTrue {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w < n + C.gates.length, wval C (fun _ : Fin n => true) w = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · rw [wval_input C _ w hlt]
    · have hj : w - n < C.gates.length := by omega
      have hwn : w = n + (w - n) := by omega
      rw [hwn]
      have h0 : opnd C (w - n) 0 < w := by
        have := opnd_lt hAO hj 0
        omega
      have h1 : opnd C (w - n) 1 < w := by
        have := opnd_lt hAO hj 1
        omega
      have hv0 := ih (opnd C (w - n) 0) h0 (by omega)
      have hv1 := ih (opnd C (w - n) 1) h1 (by omega)
      rcases hAO.1 (gateAt C (w - n)) (gateAt_mem hj) with hop | hop
      · rw [wval_gate_and hAO _ hj hop, hv0, hv1]; rfl
      · rw [wval_gate_or hAO _ hj hop, hv0, hv1]; rfl

lemma wval_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {x y : Fin n → Bool}
    (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w, wval C x w = true → wval C y w = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hx
    by_cases hlt : w < n
    · rw [wval_input C x w hlt] at hx
      rw [wval_input C y w hlt]
      exact hxy ⟨w, hlt⟩ hx
    · by_cases hw : w < n + C.gates.length
      · have hj : w - n < C.gates.length := by omega
        have hwn : w = n + (w - n) := by omega
        rw [hwn] at hx ⊢
        have h0 : opnd C (w - n) 0 < w := by
          have := opnd_lt hAO hj 0
          omega
        have h1 : opnd C (w - n) 1 < w := by
          have := opnd_lt hAO hj 1
          omega
        rcases hAO.1 (gateAt C (w - n)) (gateAt_mem hj) with hop | hop
        · rw [wval_gate_and hAO x hj hop, Bool.and_eq_true] at hx
          rw [wval_gate_and hAO y hj hop, Bool.and_eq_true]
          exact ⟨ih _ h0 hx.1, ih _ h1 hx.2⟩
        · rw [wval_gate_or hAO x hj hop, Bool.or_eq_true] at hx
          rw [wval_gate_or hAO y hj hop, Bool.or_eq_true]
          exact hx.elim (fun h => Or.inl (ih _ h0 h)) (fun h => Or.inr (ih _ h1 h))
      · rw [wval_ge_len C x (by omega)] at hx
        cases hx

lemma foldl_cones_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons gt rest ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_cones_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (coneStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons gt rest ih =>
    simp only [List.foldl_cons]
    have hlt : i < (coneStep n acc gt).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [ih _ hlt]
    simp [coneStep, List.getD, List.getElem?_append_left hi]

lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones
  simpa using foldl_cones_len n C.gates []

lemma inCone_lt_len {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : j < C.gates.length := by
  unfold InCone at h
  by_contra hge
  have hle : (cones n C).length ≤ j := by rw [cones_length]; omega
  rw [List.getD_eq_default _ _ hle] at h
  simp at h

lemma inCone_iff {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone cones
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    have hg : gateAt C j = C.gates[j] := by
      unfold gateAt
      exact List.getD_eq_getElem _ _ hj
    rw [hg]
    simpa using (List.take_append_drop j C.gates).symm.trans (by
      congr 1
      exact (List.cons_getElem_drop_succ (h := hj)).symm)
  set pre := (C.gates.take j).foldl (coneStep n) []
  have hpre_len : pre.length = j := by
    have h1 := foldl_cones_len n (C.gates.take j) []
    simp only [List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at h1
    exact h1
  have h_eq : C.gates.foldl (coneStep n) [] =
      (C.gates.drop (j + 1)).foldl (coneStep n) (coneStep n pre (gateAt C j)) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have h_pre_get : ∀ k < j, (C.gates.foldl (coneStep n) []).getD k [] = pre.getD k [] := by
    intro k hk
    rw [h_eq]
    have hk1 : k < (coneStep n pre (gateAt C j)).length := by
      simp only [coneStep, List.length_append, List.length_singleton, hpre_len]
      omega
    rw [foldl_cones_getD_lt _ _ _ k hk1]
    have hk2 : k < pre.length := by omega
    simp [coneStep, List.getD, List.getElem?_append_left hk2]
  have h_j : (C.gates.foldl (coneStep n) []).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: pre.getD (w - n) []) := by
    rw [h_eq]
    have hlt : j < (coneStep n pre (gateAt C j)).length := by
      simp only [coneStep, List.length_append, List.length_singleton, hpre_len]
      omega
    rw [foldl_cones_getD_lt _ _ _ j hlt]
    have hle : pre.length ≤ j := by omega
    simp [coneStep, List.getD, List.getElem?_append_right hle, hpre_len]
  rw [h_j]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hwm, hwn, hwlt⟩, hmem⟩
    refine ⟨w, hwm, hwn, hwlt, ?_⟩
    rcases hmem with rfl | hmem
    · exact Or.inl rfl
    · right
      rw [← h_pre_get (w - n) (by omega)] at hmem
      exact hmem
  · rintro ⟨w, hwm, hwn, hwlt, hmem⟩
    refine ⟨w, ⟨hwm, hwn, hwlt⟩, ?_⟩
    rcases hmem with rfl | hmem
    · exact Or.inl rfl
    · right
      rw [h_pre_get (w - n) (by omega)] at hmem
      exact hmem

lemma inCone_lt {n : ℕ} {C : Circuit} {i j : ℕ} : InCone n C i j → i < j := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro h
    have hj : j < C.gates.length := inCone_lt_len h
    rw [inCone_iff hj] at h
    rcases h with ⟨w, _, hwn, hwlt, rfl | hsub⟩
    · omega
    · have h1 := ih (w - n) (by omega) hsub
      omega

lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma graphFun_unitInput_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    graphFun G ∅ (unitInput v) = false := by
  cases hf : graphFun G ∅ (unitInput v) with
  | false => rfl
  | true =>
    rw [graphFun_iff] at hf
    rcases hf with ⟨u, w, hadj, hu, hw⟩
    simp only [unitInput, decide_eq_true_eq] at hu hw
    subst hu; subst hw
    exact (G.ne_of_adj hadj rfl).elim

lemma graphFun_pairInput_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  rw [graphFun_iff]
  constructor
  · rintro ⟨a, b, hadj, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.ne_of_adj hadj rfl).elim
    · exact hadj
    · exact hadj.symm
    · exact (G.ne_of_adj hadj rfl).elim
  · intro hadj
    exact ⟨u, v, hadj, by simp [pairInput], by simp [pairInput]⟩

def tripleInput {n : ℕ} (u w z : Fin n) : Fin n → Bool :=
  fun t => decide (t = u ∨ t = w ∨ t = z)

lemma graphFun_tripleInput_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u w z : Fin n) :
    graphFun G ∅ (tripleInput u w z) = true ↔ G.Adj u w ∨ G.Adj u z ∨ G.Adj w z := by
  rw [graphFun_iff]
  constructor
  · rintro ⟨a, b, hadj, ha, hb⟩
    simp only [tripleInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact (G.ne_of_adj hadj rfl).elim
    · exact Or.inl hadj
    · exact Or.inr (Or.inl hadj)
    · exact Or.inl hadj.symm
    · exact (G.ne_of_adj hadj rfl).elim
    · exact Or.inr (Or.inr hadj)
    · exact Or.inr (Or.inl hadj.symm)
    · exact Or.inr (Or.inr hadj.symm)
    · exact (G.ne_of_adj hadj rfl).elim
  · rintro (h | h | h)
    · exact ⟨u, w, h, by simp [tripleInput], by simp [tripleInput]⟩
    · exact ⟨u, z, h, by simp [tripleInput], by simp [tripleInput]⟩
    · exact ⟨w, z, h, by simp [tripleInput], by simp [tripleInput]⟩

lemma noFourCycle_unique {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hC4 : NoFourCycle G) {a b z1 z2 : Fin n} (hab : a ≠ b)
    (ha1 : G.Adj a z1) (hb1 : G.Adj b z1) (ha2 : G.Adj a z2) (hb2 : G.Adj b z2) :
    z1 = z2 := by
  have hcard := hC4 a b hab
  have h1 : z1 ∈ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
    simp [ha1, hb1]
  have h2 : z2 ∈ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
    simp [ha2, hb2]
  exact Finset.card_le_one.mp hcard z1 h1 z2 h2

lemma circuitFun_eq_graphFun_of {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D : Circuit} (hAO : IsAO2 n D)
    (hle : ∀ x : Fin n → Bool, circuitFun n D x = true → graphFun G ∅ x = true)
    (hge : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = graphFun G ∅ := by
  funext x
  cases hD : circuitFun n D x with
  | true =>
    exact (hle x hD).symm
  | false =>
    cases hF : graphFun G ∅ x with
    | false => rfl
    | true =>
      rw [graphFun_iff] at hF
      rcases hF with ⟨u, v, hadj, hu, hv⟩
      have hp : circuitFun n D (pairInput u v) = true := hge u v hadj
      have hmono : circuitFun n D x = true := wval_mono hAO (fun i hi => by
        simp only [pairInput, decide_eq_true_eq] at hi
        rcases hi with rfl | rfl <;> assumption) D.output hp
      rw [hD] at hmono
      cases hmono

def WireBelowF {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true

lemma not_wireBelowF_input {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    {w : ℕ} (hw : w < n) : ¬ WireBelowF G C w := by
  intro h
  have h1 : wval C (unitInput ⟨w, hw⟩) w = true := by
    rw [wval_input C _ w hw]
    simp [unitInput]
  have h2 := h (unitInput ⟨w, hw⟩) h1
  rw [graphFun_unitInput_false] at h2
  cases h2

lemma wireBelowF_gate_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    WireBelowF G C (n + k) ↔ BelowF G C k := Iff.rfl

def usesG (n : ℕ) (C : Circuit) (g : ℕ) (w : ℕ) : Bool :=
  if w < n then false
  else if w = n + g then true
  else
    let k := w - n
    if k < C.gates.length then
      if h : opnd C k 0 < w ∧ opnd C k 1 < w then
        usesG n C g (opnd C k 0) || usesG n C g (opnd C k 1)
      else false
    else false
termination_by w
decreasing_by
  · exact h.1
  · exact h.2

def varSet (n : ℕ) (C : Circuit) (g : ℕ) (w : ℕ) : Finset (Fin n) :=
  if h : w < n then {⟨w, h⟩}
  else if w = n + g then ∅
  else
    let k := w - n
    if k < C.gates.length then
      if h2 : opnd C k 0 < w ∧ opnd C k 1 < w then
        varSet n C g (opnd C k 0) ∪ varSet n C g (opnd C k 1)
      else ∅
    else ∅
termination_by w
decreasing_by
  · exact h2.1
  · exact h2.2

lemma usesG_input (n : ℕ) (C : Circuit) (g w : ℕ) (hw : w < n) :
    usesG n C g w = false := by
  rw [usesG]; simp [hw]

lemma usesG_g (n : ℕ) (C : Circuit) (g : ℕ) :
    usesG n C g (n + g) = true := by
  rw [usesG]
  have h1 : ¬ n + g < n := by omega
  simp [h1]

lemma usesG_gate {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (g k : ℕ)
    (hk : k < C.gates.length) (hkg : k ≠ g) :
    usesG n C g (n + k) = (usesG n C g (opnd C k 0) || usesG n C g (opnd C k 1)) := by
  rw [usesG]
  have h1 : ¬ n + k < n := by omega
  have h3 : n + k - n = k := by omega
  have hlt0 : opnd C k 0 < n + k := opnd_lt hAO hk 0
  have hlt1 : opnd C k 1 < n + k := opnd_lt hAO hk 1
  simp [h1, hkg, h3, hk, hlt0, hlt1]

lemma usesG_lt_g {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (g : ℕ) :
    ∀ w < n + g, usesG n C g w = false := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · exact usesG_input n C g w hlt
    · by_cases hk : w - n < C.gates.length
      · have hwn : w = n + (w - n) := by omega
        have hkg : w - n ≠ g := by omega
        rw [hwn, usesG_gate hAO g (w - n) hk hkg]
        have h0 : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
        have h1 : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
        rw [ih _ h0 (by omega), ih _ h1 (by omega)]
        rfl
      · rw [usesG]
        have hne : w ≠ n + g := by omega
        simp [hlt, hne, hk]

lemma varSet_input (n : ℕ) (C : Circuit) (g w : ℕ) (hw : w < n) :
    varSet n C g w = {⟨w, hw⟩} := by
  rw [varSet]; simp [hw]

lemma varSet_g (n : ℕ) (C : Circuit) (g : ℕ) :
    varSet n C g (n + g) = ∅ := by
  rw [varSet]
  have h1 : ¬ n + g < n := by omega
  simp [h1]

lemma varSet_gate {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (g k : ℕ)
    (hk : k < C.gates.length) (hkg : k ≠ g) :
    varSet n C g (n + k) = varSet n C g (opnd C k 0) ∪ varSet n C g (opnd C k 1) := by
  rw [varSet]
  have h1 : ¬ n + k < n := by omega
  have h3 : n + k - n = k := by omega
  have hlt0 : opnd C k 0 < n + k := opnd_lt hAO hk 0
  have hlt1 : opnd C k 1 < n + k := opnd_lt hAO hk 1
  simp [h1, hkg, h3, hk, hlt0, hlt1]

def zSet (n : ℕ) (C : Circuit) (g : ℕ) : Finset (Fin n) :=
  (Finset.range C.gates.length).biUnion fun a =>
    match (gateAt C a).op with
    | GateOp.and =>
      if a ≠ g then
        (if usesG n C g (opnd C a 0) = true then varSet n C g (opnd C a 1) else ∅) ∪
        (if usesG n C g (opnd C a 1) = true then varSet n C g (opnd C a 0) else ∅)
      else ∅
    | _ => ∅

def delMap (n g r w : ℕ) : ℕ :=
  if w < n + g then w
  else if w = n + g then r
  else w - 1

def delGateMap (g k : ℕ) : ℕ :=
  if k < g then k else k - 1

lemma delMap_gate (n g r k : ℕ) (hkg : k ≠ g) :
    delMap n g r (n + k) = n + delGateMap g k := by
  unfold delMap delGateMap
  split_ifs <;> omega

def delCircuit (n : ℕ) (C : Circuit) (g r : ℕ) : Circuit :=
  { gates := List.ofFn fun i : Fin (C.gates.length - 1) =>
      let src := if i.val < g then i.val else i.val + 1
      let gt := gateAt C src
      ⟨gt.op, gt.inputs.map (delMap n g r)⟩
    output := delMap n g r C.output }

lemma delCircuit_len (n : ℕ) (C : Circuit) (g r : ℕ) :
    (delCircuit n C g r).gates.length = C.gates.length - 1 := by
  simp [delCircuit]

lemma delCircuit_size (n : ℕ) (C : Circuit) (g r : ℕ) :
    (delCircuit n C g r).size ≤ C.size := by
  simp [Circuit.size, delCircuit]

lemma delCircuit_gateAt {n : ℕ} {C : Circuit} {g r i : ℕ} (hi : i < C.gates.length - 1) :
    gateAt (delCircuit n C g r) i =
      let src := if i < g then i else i + 1
      let gt := gateAt C src
      ⟨gt.op, gt.inputs.map (delMap n g r)⟩ := by
  have hlt : i < (delCircuit n C g r).gates.length := by rw [delCircuit_len]; exact hi
  conv_lhs => unfold gateAt
  rw [List.getD_eq_getElem _ _ hlt]
  simp [delCircuit]

lemma delCircuit_gateAt_src {n : ℕ} {C : Circuit} {g r k : ℕ}
    (hg : g < C.gates.length) (hk : k < C.gates.length) (hkg : k ≠ g) :
    gateAt (delCircuit n C g r) (delGateMap g k) =
      ⟨(gateAt C k).op, (gateAt C k).inputs.map (delMap n g r)⟩ := by
  have hi : delGateMap g k < C.gates.length - 1 := by
    unfold delGateMap; split_ifs <;> omega
  rw [delCircuit_gateAt hi]
  have hsrc : (if delGateMap g k < g then delGateMap g k else delGateMap g k + 1) = k := by
    unfold delGateMap; split_ifs <;> omega
  simp [hsrc]

lemma delCircuit_isAO2 {n : ℕ} {C : Circuit} {g r : ℕ}
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hr : r < n + g) :
    IsAO2 n (delCircuit n C g r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro gt hgt
    simp only [delCircuit, List.mem_ofFn] at hgt
    rcases hgt with ⟨i, rfl⟩
    have hsrc : (if i.val < g then i.val else i.val + 1) < C.gates.length := by
      split_ifs <;> omega
    exact hAO.1 (gateAt C (if i.val < g then i.val else i.val + 1)) (gateAt_mem hsrc)
  · intro i hi w hw
    rw [delCircuit_len] at hi
    rw [delCircuit_gateAt hi] at hw
    simp only [List.mem_map] at hw
    rcases hw with ⟨u, hu, rfl⟩
    by_cases hig : i < g
    · simp only [hig, ↓reduceIte] at hu
      have hult : u < n + i := hAO.2.1 i (by omega) u hu
      unfold delMap
      split_ifs <;> omega
    · simp only [hig, ↓reduceIte] at hu
      have hult : u < n + (i + 1) := hAO.2.1 (i + 1) (by omega) u hu
      unfold delMap
      split_ifs <;> omega
  · intro gt hgt
    simp only [delCircuit, List.mem_ofFn] at hgt
    rcases hgt with ⟨i, rfl⟩
    have hsrc : (if i.val < g then i.val else i.val + 1) < C.gates.length := by
      split_ifs <;> omega
    simp [hAO.2.2 _ (gateAt_mem hsrc)]

lemma delCircuit_opnd {n : ℕ} {C : Circuit} {g r k : ℕ}
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hk : k < C.gates.length) (hkg : k ≠ g) (b : Fin 2) :
    opnd (delCircuit n C g r) (delGateMap g k) b = delMap n g r (opnd C k b) := by
  unfold opnd
  rw [delCircuit_gateAt_src hg hk hkg, gate_inputs_eq hAO hk]
  fin_cases b <;> simp [opnd]

lemma delCircuit_wval_lt {n : ℕ} {C : Circuit} {g r : ℕ}
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hr : r < n + g) (x : Fin n → Bool) :
    ∀ w < n + g, wval (delCircuit n C g r) x w = wval C x w := by
  have hAO' := delCircuit_isAO2 hAO hg hr
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · rw [wval_input _ x w hlt, wval_input _ x w hlt]
    · have hk : w - n < g := by omega
      have hklt : w - n < C.gates.length := by omega
      have hkg : w - n ≠ g := by omega
      have hwn : w = n + (w - n) := by omega
      have hdgm : delGateMap g (w - n) = w - n := by simp [delGateMap, hk]
      have hk' : w - n < (delCircuit n C g r).gates.length := by rw [delCircuit_len]; omega
      have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hklt 0; omega
      have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hklt 1; omega
      have hop0 : opnd (delCircuit n C g r) (w - n) 0 = opnd C (w - n) 0 := by
        conv_lhs => rw [← hdgm]
        rw [delCircuit_opnd hAO hg hklt hkg 0]
        unfold delMap; split_ifs <;> omega
      have hop1 : opnd (delCircuit n C g r) (w - n) 1 = opnd C (w - n) 1 := by
        conv_lhs => rw [← hdgm]
        rw [delCircuit_opnd hAO hg hklt hkg 1]
        unfold delMap; split_ifs <;> omega
      have hgate : (gateAt (delCircuit n C g r) (w - n)).op = (gateAt C (w - n)).op := by
        conv_lhs => rw [← hdgm]
        rw [delCircuit_gateAt_src hg hklt hkg]
      rw [hwn]
      rcases hAO.1 _ (gateAt_mem hklt) with hop | hop
      · rw [wval_gate_and hAO' x hk' (hgate.trans hop), wval_gate_and hAO x hklt hop,
          hop0, hop1, ih _ h0lt (by omega), ih _ h1lt (by omega)]
      · rw [wval_gate_or hAO' x hk' (hgate.trans hop), wval_gate_or hAO x hklt hop,
          hop0, hop1, ih _ h0lt (by omega), ih _ h1lt (by omega)]

lemma delCircuit_wval_le {n : ℕ} {C : Circuit} {g r : ℕ}
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hr : r < n + g) (x : Fin n → Bool)
    (hle : wval C x r = true → gateVal n C g x = true) :
    ∀ w < n + C.gates.length, wval (delCircuit n C g r) x (delMap n g r w) = true → wval C x w = true := by
  have hAO' := delCircuit_isAO2 hAO hg hr
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hD
    by_cases hlt : w < n + g
    · have hm : delMap n g r w = w := by simp [delMap, hlt]
      rw [hm, delCircuit_wval_lt hAO hg hr x w hlt] at hD
      exact hD
    · by_cases hwg : w = n + g
      · subst hwg
        have hm : delMap n g r (n + g) = r := by simp [delMap]
        rw [hm, delCircuit_wval_lt hAO hg hr x r hr] at hD
        exact hle hD
      · have hk : w - n < C.gates.length := by omega
        have hkg : w - n ≠ g := by omega
        have hwn : w = n + (w - n) := by omega
        have hdm : delMap n g r w = n + delGateMap g (w - n) := by
          conv_lhs => rw [hwn]
          exact delMap_gate n g r (w - n) hkg
        have hk' : delGateMap g (w - n) < (delCircuit n C g r).gates.length := by
          rw [delCircuit_len]; unfold delGateMap; split_ifs <;> omega
        have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
        have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
        have hgate : (gateAt (delCircuit n C g r) (delGateMap g (w - n))).op = (gateAt C (w - n)).op := by
          rw [delCircuit_gateAt_src hg hk hkg]
        rw [hdm] at hD
        rw [hwn]
        rcases hAO.1 _ (gateAt_mem hk) with hop | hop
        · rw [wval_gate_and hAO' x hk' (hgate.trans hop), Bool.and_eq_true,
            delCircuit_opnd hAO hg hk hkg 0, delCircuit_opnd hAO hg hk hkg 1] at hD
          rw [wval_gate_and hAO x hk hop, Bool.and_eq_true]
          exact ⟨ih _ h0lt (by omega) hD.1, ih _ h1lt (by omega) hD.2⟩
        · rw [wval_gate_or hAO' x hk' (hgate.trans hop), Bool.or_eq_true,
            delCircuit_opnd hAO hg hk hkg 0, delCircuit_opnd hAO hg hk hkg 1] at hD
          rw [wval_gate_or hAO x hk hop, Bool.or_eq_true]
          exact hD.elim (fun h => Or.inl (ih _ h0lt (by omega) h))
            (fun h => Or.inr (ih _ h1lt (by omega) h))

lemma delCircuit_wval_ge {n : ℕ} {C : Circuit} {g r : ℕ}
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hr : r < n + g) (x : Fin n → Bool)
    (hge : gateVal n C g x = true → wval C x r = true) :
    ∀ w < n + C.gates.length, wval C x w = true → wval (delCircuit n C g r) x (delMap n g r w) = true := by
  have hAO' := delCircuit_isAO2 hAO hg hr
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hC
    by_cases hlt : w < n + g
    · have hm : delMap n g r w = w := by simp [delMap, hlt]
      rw [hm, delCircuit_wval_lt hAO hg hr x w hlt]
      exact hC
    · by_cases hwg : w = n + g
      · subst hwg
        have hm : delMap n g r (n + g) = r := by simp [delMap]
        rw [hm, delCircuit_wval_lt hAO hg hr x r hr]
        exact hge hC
      · have hk : w - n < C.gates.length := by omega
        have hkg : w - n ≠ g := by omega
        have hwn : w = n + (w - n) := by omega
        have hdm : delMap n g r w = n + delGateMap g (w - n) := by
          conv_lhs => rw [hwn]
          exact delMap_gate n g r (w - n) hkg
        have hk' : delGateMap g (w - n) < (delCircuit n C g r).gates.length := by
          rw [delCircuit_len]; unfold delGateMap; split_ifs <;> omega
        have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
        have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
        have hgate : (gateAt (delCircuit n C g r) (delGateMap g (w - n))).op = (gateAt C (w - n)).op := by
          rw [delCircuit_gateAt_src hg hk hkg]
        rw [hdm]
        rw [hwn] at hC
        rcases hAO.1 _ (gateAt_mem hk) with hop | hop
        · rw [wval_gate_and hAO x hk hop, Bool.and_eq_true] at hC
          rw [wval_gate_and hAO' x hk' (hgate.trans hop), Bool.and_eq_true,
            delCircuit_opnd hAO hg hk hkg 0, delCircuit_opnd hAO hg hk hkg 1]
          exact ⟨ih _ h0lt (by omega) hC.1, ih _ h1lt (by omega) hC.2⟩
        · rw [wval_gate_or hAO x hk hop, Bool.or_eq_true] at hC
          rw [wval_gate_or hAO' x hk' (hgate.trans hop), Bool.or_eq_true,
            delCircuit_opnd hAO hg hk hkg 0, delCircuit_opnd hAO hg hk hkg 1]
          exact hC.elim (fun h => Or.inl (ih _ h0lt (by omega) h))
            (fun h => Or.inr (ih _ h1lt (by omega) h))

def isTwoSided {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (v : Fin n) (g w : ℕ) : Prop :=
  w < n + C.gates.length ∧ ¬ WireBelowF G C w ∧
    (∃ u ∈ varSet n C g w, s u = s v) ∧ (∃ u ∈ varSet n C g w, s u ≠ s v)

def isRSided {n : ℕ} (C : Circuit) (s : Fin n → Bool) (v : Fin n) (g w : ℕ) : Prop :=
  ∀ u ∈ varSet n C g w, s u ≠ s v

def restrictMap {n : ℕ} (C : Circuit) (s : Fin n → Bool) (v : Fin n) (g w : ℕ) : ℕ :=
  if ∀ u ∈ varSet n C g w, s u ≠ s v then v.val else w

def restrictTwoSided {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (v : Fin n) (g : ℕ) : Circuit :=
  { gates := List.ofFn fun i : Fin C.gates.length =>
      let gt := gateAt C i.val
      if ¬ BelowF G C i.val ∧ (∃ u ∈ varSet n C g (n + i.val), s u = s v) ∧
          (∃ u ∈ varSet n C g (n + i.val), s u ≠ s v) then
        ⟨gt.op, gt.inputs.map (restrictMap C s v g)⟩
      else gt
    output := C.output }

lemma restrictTwoSided_len {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (v : Fin n) (g : ℕ) :
    (restrictTwoSided G C s v g).gates.length = C.gates.length := by
  simp [restrictTwoSided]

lemma restrictTwoSided_gateAt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (v : Fin n) (g k : ℕ) (hk : k < C.gates.length) :
    gateAt (restrictTwoSided G C s v g) k =
      if ¬ BelowF G C k ∧ (∃ u ∈ varSet n C g (n + k), s u = s v) ∧
          (∃ u ∈ varSet n C g (n + k), s u ≠ s v) then
        ⟨(gateAt C k).op, (gateAt C k).inputs.map (restrictMap C s v g)⟩
      else gateAt C k := by
  have hlt : k < (restrictTwoSided G C s v g).gates.length := by rw [restrictTwoSided_len]; exact hk
  conv_lhs => unfold gateAt
  rw [List.getD_eq_getElem _ _ hlt]
  simp [restrictTwoSided]

lemma restrictTwoSided_isAO2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (s : Fin n → Bool) (v : Fin n) (g : ℕ) :
    IsAO2 n (restrictTwoSided G C s v g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro gt hgt
    simp only [restrictTwoSided, List.mem_ofFn] at hgt
    rcases hgt with ⟨i, rfl⟩
    split_ifs
    · exact hAO.1 (gateAt C i.val) (gateAt_mem i.isLt)
    · exact hAO.1 (gateAt C i.val) (gateAt_mem i.isLt)
  · intro k hk w hw
    rw [restrictTwoSided_len] at hk
    rw [restrictTwoSided_gateAt G C s v g k hk] at hw
    split_ifs at hw with hts
    · simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      unfold restrictMap
      split_ifs
      · omega
      · exact hAO.2.1 k hk u hu
    · exact hAO.2.1 k hk w hw
  · intro gt hgt
    simp only [restrictTwoSided, List.mem_ofFn] at hgt
    rcases hgt with ⟨i, rfl⟩
    split_ifs
    · simp [hAO.2.2 _ (gateAt_mem i.isLt)]
    · exact hAO.2.2 _ (gateAt_mem i.isLt)

def remapC (n jb g w : ℕ) : ℕ :=
  if w < n + jb then w
  else if w < n + g then w - 1
  else w

def remapCGate (jb g k : ℕ) : ℕ :=
  if k < jb then k
  else if k < g then k - 1
  else k

lemma remapC_gate (n jb g k : ℕ) (hkjb : k ≠ jb) :
    remapC n jb g (n + k) = n + remapCGate jb g k := by
  unfold remapC remapCGate
  split_ifs <;> omega

def rewriteCircuit (n : ℕ) (C : Circuit) (jb g aW : ℕ) (v m : Fin n) : Circuit :=
  { gates := List.ofFn fun i : Fin C.gates.length =>
      if i.val < jb then
        gateAt C i.val
      else if i.val + 1 < g then
        let gt := gateAt C (i.val + 1)
        ⟨gt.op, gt.inputs.map (remapC n jb g)⟩
      else if i.val + 1 = g then
        ⟨GateOp.and, [remapC n jb g aW, m.val]⟩
      else if i.val = g then
        ⟨GateOp.or, [v.val, n + (g - 1)]⟩
      else
        let gt := gateAt C i.val
        ⟨gt.op, gt.inputs.map (remapC n jb g)⟩
    output := C.output }

lemma rewriteCircuit_len (n : ℕ) (C : Circuit) (jb g aW : ℕ) (v m : Fin n) :
    (rewriteCircuit n C jb g aW v m).gates.length = C.gates.length := by
  simp [rewriteCircuit]

lemma rewriteCircuit_size (n : ℕ) (C : Circuit) (jb g aW : ℕ) (v m : Fin n) :
    (rewriteCircuit n C jb g aW v m).size ≤ C.size := by
  simp [Circuit.size, rewriteCircuit]

lemma rewriteCircuit_gateAt {n : ℕ} {C : Circuit} {jb g aW i : ℕ} {v m : Fin n}
    (hi : i < C.gates.length) :
    gateAt (rewriteCircuit n C jb g aW v m) i =
      if i < jb then
        gateAt C i
      else if i + 1 < g then
        let gt := gateAt C (i + 1)
        ⟨gt.op, gt.inputs.map (remapC n jb g)⟩
      else if i + 1 = g then
        ⟨GateOp.and, [remapC n jb g aW, m.val]⟩
      else if i = g then
        ⟨GateOp.or, [v.val, n + (g - 1)]⟩
      else
        let gt := gateAt C i
        ⟨gt.op, gt.inputs.map (remapC n jb g)⟩ := by
  have hlt : i < (rewriteCircuit n C jb g aW v m).gates.length := by rw [rewriteCircuit_len]; exact hi
  conv_lhs => unfold gateAt
  rw [List.getD_eq_getElem _ _ hlt]
  simp [rewriteCircuit]

lemma rewriteCircuit_isAO2 {n : ℕ} {C : Circuit} {jb g aW : ℕ} (v m : Fin n)
    (hAO : IsAO2 n C) (hjbg : jb < g) (hg : g < C.gates.length)
    (haWlt : aW < n + g) (haWne : aW ≠ n + jb)
    (hno : ∀ k < C.gates.length, k ≠ g → n + jb ∉ (gateAt C k).inputs) :
    IsAO2 n (rewriteCircuit n C jb g aW v m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro gt hgt
    simp only [rewriteCircuit, List.mem_ofFn] at hgt
    rcases hgt with ⟨i, rfl⟩
    split_ifs with h1 h2 h3 h4
    · exact hAO.1 (gateAt C i.val) (gateAt_mem i.isLt)
    · exact hAO.1 (gateAt C (i.val + 1)) (gateAt_mem (by omega))
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact hAO.1 (gateAt C i.val) (gateAt_mem i.isLt)
  · intro i hi w hw
    rw [rewriteCircuit_len] at hi
    rw [rewriteCircuit_gateAt hi] at hw
    split_ifs at hw with h1 h2 h3 h4
    · exact hAO.2.1 i hi w hw
    · simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      have hult := hAO.2.1 (i + 1) (by omega) u hu
      have hune : u ≠ n + jb := fun heq => hno (i + 1) (by omega) (by omega) (heq ▸ hu)
      unfold remapC
      split_ifs <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · unfold remapC; split_ifs <;> omega
      · omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> omega
    · simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      have hult := hAO.2.1 i hi u hu
      unfold remapC
      split_ifs <;> omega
  · intro gt hgt
    simp only [rewriteCircuit, List.mem_ofFn] at hgt
    rcases hgt with ⟨i, rfl⟩
    split_ifs with h1 h2 h3 h4
    · exact hAO.2.2 (gateAt C i.val) (gateAt_mem i.isLt)
    · have hlt2 : i.val + 1 < C.gates.length := by omega
      simp [hAO.2.2 (gateAt C (i.val + 1)) (gateAt_mem hlt2)]
    · rfl
    · rfl
    · simp [hAO.2.2 (gateAt C i.val) (gateAt_mem i.isLt)]

lemma rewriteCircuit_wval_lt_g {n : ℕ} {C : Circuit} {jb g aW : ℕ} {v m : Fin n}
    (hAO : IsAO2 n C) (hjbg : jb < g) (hg : g < C.gates.length)
    (haWlt : aW < n + g) (haWne : aW ≠ n + jb)
    (hno : ∀ k < C.gates.length, k ≠ g → n + jb ∉ (gateAt C k).inputs)
    (x : Fin n → Bool) :
    ∀ w < n + g, w ≠ n + jb → wval (rewriteCircuit n C jb g aW v m) x (remapC n jb g w) = wval C x w := by
  have hAO' := rewriteCircuit_isAO2 v m hAO hjbg hg haWlt haWne hno
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hwne
    by_cases hlt : w < n
    · have hm : remapC n jb g w = w := by unfold remapC; split_ifs <;> omega
      rw [hm, wval_input _ x w hlt, wval_input _ x w hlt]
    · have hk : w - n < g := by omega
      have hklt : w - n < C.gates.length := by omega
      have hkjb : w - n ≠ jb := by omega
      have hkg : w - n ≠ g := by omega
      have hwn : w = n + (w - n) := by omega
      have hrm : remapC n jb g w = n + remapCGate jb g (w - n) := by
        conv_lhs => rw [hwn]
        exact remapC_gate n jb g (w - n) hkjb
      have hi : remapCGate jb g (w - n) < (rewriteCircuit n C jb g aW v m).gates.length := by
        rw [rewriteCircuit_len]; unfold remapCGate; split_ifs <;> omega
      have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hklt 0; omega
      have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hklt 1; omega
      have h0ne : opnd C (w - n) 0 ≠ n + jb :=
        fun heq => hno (w - n) hklt hkg (heq ▸ opnd_mem hAO hklt 0)
      have h1ne : opnd C (w - n) 1 ≠ n + jb :=
        fun heq => hno (w - n) hklt hkg (heq ▸ opnd_mem hAO hklt 1)
      have hgt : gateAt (rewriteCircuit n C jb g aW v m) (remapCGate jb g (w - n)) =
          ⟨(gateAt C (w - n)).op, (gateAt C (w - n)).inputs.map (remapC n jb g)⟩ := by
        rw [rewriteCircuit_gateAt (by simpa [rewriteCircuit_len] using hi)]
        unfold remapCGate
        by_cases hltjb : w - n < jb
        · simp only [hltjb, ↓reduceIte]
          have h0m : remapC n jb g (opnd C (w - n) 0) = opnd C (w - n) 0 := by
            have := opnd_lt hAO hklt 0; unfold remapC; split_ifs <;> omega
          have h1m : remapC n jb g (opnd C (w - n) 1) = opnd C (w - n) 1 := by
            have := opnd_lt hAO hklt 1; unfold remapC; split_ifs <;> omega
          have hinp := gate_inputs_eq hAO hklt
          cases hc : gateAt C (w - n) with
          | mk op ins =>
            rw [hc] at hinp
            dsimp at hinp
            rw [hinp]
            simp [h0m, h1m]
        · have hif1 : ¬ w - n - 1 < jb := by omega
          have hif2 : w - n - 1 + 1 < g := by omega
          have heq : w - n - 1 + 1 = w - n := by omega
          simp only [hltjb, hk, ↓reduceIte, hif1, hif2, heq]
      have hop0 : opnd (rewriteCircuit n C jb g aW v m) (remapCGate jb g (w - n)) 0 =
          remapC n jb g (opnd C (w - n) 0) := by
        unfold opnd; rw [hgt, gate_inputs_eq hAO hklt]; rfl
      have hop1 : opnd (rewriteCircuit n C jb g aW v m) (remapCGate jb g (w - n)) 1 =
          remapC n jb g (opnd C (w - n) 1) := by
        unfold opnd; rw [hgt, gate_inputs_eq hAO hklt]; rfl
      have hop_eq : (gateAt (rewriteCircuit n C jb g aW v m) (remapCGate jb g (w - n))).op =
          (gateAt C (w - n)).op := by rw [hgt]
      rw [hrm]
      conv_rhs => rw [hwn]
      rcases hAO.1 _ (gateAt_mem hklt) with hop | hop
      · rw [wval_gate_and hAO' x hi (hop_eq.trans hop), wval_gate_and hAO x hklt hop,
          hop0, hop1, ih _ h0lt (by omega) h0ne, ih _ h1lt (by omega) h1ne]
      · rw [wval_gate_or hAO' x hi (hop_eq.trans hop), wval_gate_or hAO x hklt hop,
          hop0, hop1, ih _ h0lt (by omega) h0ne, ih _ h1lt (by omega) h1ne]

lemma rewriteCircuit_wval_and {n : ℕ} {C : Circuit} {jb g aW : ℕ} {v m : Fin n}
    (hAO : IsAO2 n C) (hjbg : jb < g) (hg : g < C.gates.length)
    (haWlt : aW < n + g) (haWne : aW ≠ n + jb)
    (hno : ∀ k < C.gates.length, k ≠ g → n + jb ∉ (gateAt C k).inputs)
    (x : Fin n → Bool) :
    gateVal n (rewriteCircuit n C jb g aW v m) (g - 1) x = (wval C x aW && x m) := by
  have hAO' := rewriteCircuit_isAO2 v m hAO hjbg hg haWlt haWne hno
  have hi : g - 1 < (rewriteCircuit n C jb g aW v m).gates.length := by
    rw [rewriteCircuit_len]; omega
  have hgt : gateAt (rewriteCircuit n C jb g aW v m) (g - 1) =
      ⟨GateOp.and, [remapC n jb g aW, m.val]⟩ := by
    rw [rewriteCircuit_gateAt (by omega)]
    have h1 : ¬ g - 1 < jb := by omega
    have h3 : g - 1 + 1 = g := by omega
    simp [h1, h3]
  have hop : (gateAt (rewriteCircuit n C jb g aW v m) (g - 1)).op = GateOp.and := by rw [hgt]
  have hop0 : opnd (rewriteCircuit n C jb g aW v m) (g - 1) 0 = remapC n jb g aW := by
    unfold opnd; rw [hgt]; rfl
  have hop1 : opnd (rewriteCircuit n C jb g aW v m) (g - 1) 1 = m.val := by
    unfold opnd; rw [hgt]; rfl
  change wval (rewriteCircuit n C jb g aW v m) x (n + (g - 1)) = _
  rw [wval_gate_and hAO' x hi hop, hop0, hop1,
    rewriteCircuit_wval_lt_g hAO hjbg hg haWlt haWne hno x aW haWlt haWne,
    wval_input _ x m.val m.isLt]

lemma rewriteCircuit_wval_g {n : ℕ} {C : Circuit} {jb g aW : ℕ} {v m : Fin n}
    (hAO : IsAO2 n C) (hjbg : jb < g) (hg : g < C.gates.length)
    (haWlt : aW < n + g) (haWne : aW ≠ n + jb)
    (hno : ∀ k < C.gates.length, k ≠ g → n + jb ∉ (gateAt C k).inputs)
    (x : Fin n → Bool) :
    gateVal n (rewriteCircuit n C jb g aW v m) g x = (x v || (wval C x aW && x m)) := by
  have hAO' := rewriteCircuit_isAO2 v m hAO hjbg hg haWlt haWne hno
  have hi : g < (rewriteCircuit n C jb g aW v m).gates.length := by
    rw [rewriteCircuit_len]; exact hg
  have hgt : gateAt (rewriteCircuit n C jb g aW v m) g =
      ⟨GateOp.or, [v.val, n + (g - 1)]⟩ := by
    rw [rewriteCircuit_gateAt hg]
    have h1 : ¬ g < jb := by omega
    have h2 : ¬ g + 1 < g := by omega
    simp [h1, h2]
  have hop : (gateAt (rewriteCircuit n C jb g aW v m) g).op = GateOp.or := by rw [hgt]
  have hop0 : opnd (rewriteCircuit n C jb g aW v m) g 0 = v.val := by
    unfold opnd; rw [hgt]; rfl
  have hop1 : opnd (rewriteCircuit n C jb g aW v m) g 1 = n + (g - 1) := by
    unfold opnd; rw [hgt]; rfl
  change wval (rewriteCircuit n C jb g aW v m) x (n + g) = _
  rw [wval_gate_or hAO' x hi hop, hop0, hop1, wval_input _ x v.val v.isLt]
  exact congrArg (x v || ·) (rewriteCircuit_wval_and hAO hjbg hg haWlt haWne hno x)

lemma rewriteCircuit_wval_le {n : ℕ} {C : Circuit} {jb g aW : ℕ} {v m : Fin n}
    (hAO : IsAO2 n C) (hjbg : jb < g) (hg : g < C.gates.length)
    (haWlt : aW < n + g) (haWne : aW ≠ n + jb)
    (hno : ∀ k < C.gates.length, k ≠ g → n + jb ∉ (gateAt C k).inputs)
    (x : Fin n → Bool)
    (hle_g : (x v || (wval C x aW && x m)) = true → gateVal n C g x = true) :
    ∀ w < n + C.gates.length, w ≠ n + jb →
      wval (rewriteCircuit n C jb g aW v m) x (remapC n jb g w) = true → wval C x w = true := by
  have hAO' := rewriteCircuit_isAO2 v m hAO hjbg hg haWlt haWne hno
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hwne hD
    by_cases hlt : w < n + g
    · rw [rewriteCircuit_wval_lt_g hAO hjbg hg haWlt haWne hno x w hlt hwne] at hD
      exact hD
    · by_cases hwg : w = n + g
      · subst hwg
        have hm : remapC n jb g (n + g) = n + g := by unfold remapC; split_ifs <;> omega
        rw [hm] at hD
        change gateVal n (rewriteCircuit n C jb g aW v m) g x = true at hD
        rw [rewriteCircuit_wval_g hAO hjbg hg haWlt haWne hno x] at hD
        exact hle_g hD
      · have hk : w - n < C.gates.length := by omega
        have hkg : w - n ≠ g := by omega
        have hgt_g : g < w - n := by omega
        have hwn : w = n + (w - n) := by omega
        have hm : remapC n jb g w = n + (w - n) := by unfold remapC; split_ifs <;> omega
        have hi : w - n < (rewriteCircuit n C jb g aW v m).gates.length := by
          rw [rewriteCircuit_len]; exact hk
        have hgt : gateAt (rewriteCircuit n C jb g aW v m) (w - n) =
            ⟨(gateAt C (w - n)).op, (gateAt C (w - n)).inputs.map (remapC n jb g)⟩ := by
          rw [rewriteCircuit_gateAt hk]
          have h1 : ¬ w - n < jb := by omega
          have h2 : ¬ w - n + 1 < g := by omega
          have h3 : w - n + 1 ≠ g := by omega
          simp [h1, h2, h3, hkg]
        have hop0 : opnd (rewriteCircuit n C jb g aW v m) (w - n) 0 =
            remapC n jb g (opnd C (w - n) 0) := by
          unfold opnd; rw [hgt, gate_inputs_eq hAO hk]; rfl
        have hop1 : opnd (rewriteCircuit n C jb g aW v m) (w - n) 1 =
            remapC n jb g (opnd C (w - n) 1) := by
          unfold opnd; rw [hgt, gate_inputs_eq hAO hk]; rfl
        have hop_eq : (gateAt (rewriteCircuit n C jb g aW v m) (w - n)).op = (gateAt C (w - n)).op := by
          rw [hgt]
        have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
        have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
        have h0ne : opnd C (w - n) 0 ≠ n + jb :=
          fun heq => hno (w - n) hk hkg (heq ▸ opnd_mem hAO hk 0)
        have h1ne : opnd C (w - n) 1 ≠ n + jb :=
          fun heq => hno (w - n) hk hkg (heq ▸ opnd_mem hAO hk 1)
        rw [hm] at hD
        rw [hwn]
        rcases hAO.1 _ (gateAt_mem hk) with hop | hop
        · rw [wval_gate_and hAO' x hi (hop_eq.trans hop), Bool.and_eq_true, hop0, hop1] at hD
          rw [wval_gate_and hAO x hk hop, Bool.and_eq_true]
          exact ⟨ih _ h0lt (by omega) h0ne hD.1, ih _ h1lt (by omega) h1ne hD.2⟩
        · rw [wval_gate_or hAO' x hi (hop_eq.trans hop), Bool.or_eq_true, hop0, hop1] at hD
          rw [wval_gate_or hAO x hk hop, Bool.or_eq_true]
          exact hD.elim (fun h => Or.inl (ih _ h0lt (by omega) h0ne h))
            (fun h => Or.inr (ih _ h1lt (by omega) h1ne h))

lemma or_and_or_iff {a1 a2 r1 r2 : Prop} :
    ((a1 ∨ r1) ∨ (a2 ∨ r2)) ↔ ((a1 ∨ a2) ∨ (r1 ∨ r2)) := by
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)
  · rintro ((h | h) | (h | h))
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)

lemma bool_eq_of_ne_ne {a b c : Bool} (hab : a ≠ b) (hac : a ≠ c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

structure Exceptional {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (g aW bW : ℕ) (v m : Fin n) : Prop where
  aBound : aW<n+g
  bBound : bW<n+g
  bGate : n≤bW
  distinct : aW≠bW
  aMember : aW∈(gateAt C g).inputs
  bMember : bW∈(gateAt C g).inputs
  pureA : ∀x : Fin n → Bool,wval C x aW=true ↔ ∃u∈varSet n C g aW,x u=true
  pureB : ∀x : Fin n → Bool,wval C x bW=true ↔ ∃u∈varSet n C g bW,x u=true
  gateProduct : ∀x : Fin n → Bool,gateVal n C g x=(wval C x aW && wval C x bW)
  sharedOnlyV : ∀u∈varSet n C g aW,u∈varSet n C g bW → u=v
  vInA : v∈varSet n C g aW
  vInB : v∈varSet n C g bW
  mInB : m∈varSet n C g bW
  otherA : ∃u∈varSet n C g aW,u≠v
  adjacentA : ∀u∈varSet n C g aW,G.Adj u m
  colorA : ∀u∈varSet n C g aW,s u=s v
  privateB : ∀k<C.gates.length,k≠g → bW∉(gateAt C k).inputs
  mReader : ∃a<C.gates.length,(gateAt C a).op=GateOp.and ∧ a≠g ∧
    ((usesG n C g (opnd C a 0)=true ∧ m∈varSet n C g (opnd C a 1)) ∨
     (usesG n C g (opnd C a 1)=true ∧ m∈varSet n C g (opnd C a 0)))
  oppositeUnique : ∀z∈varSet n C g bW,z∈zSet n C g → z=m
  dirtyWireFormula : ∀w<n+C.gates.length,¬WireBelowF G C w → ∀x : Fin n → Bool,
    wval C x w=true ↔ (usesG n C g w=true ∧ gateVal n C g x=true) ∨
      ∃u∈varSet n C g w,x u=true

lemma delCircuit_size_strict (n : ℕ) (C : Circuit) (g r : ℕ) (hg : g<C.gates.length) :
    (delCircuit n C g r).size<C.size := by
  change (delCircuit n C g r).gates.length<C.gates.length
  rw [delCircuit_len]
  omega

set_option maxHeartbeats 800000 in
lemma main :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C →
      (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) →
      (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) →
      g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g →
      (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) →
      (∃ v : Fin n, PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.SplitCount.unitInput v) = true) →
      (∀(aW bW : ℕ)(v m : Fin n),Exceptional G C s g aW bW v m → False) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧
        PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
        ∀ k < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.BelowF G D k := by
  intro n G _ C s g h_bip h_c4 hAO h_eq h_lift h_no_imp h_cone hg_lt hg_and hg_dirty h_clean_and h_unit h_exception
  rcases h_unit with ⟨v, hv_g⟩
  have h_out_below : WireBelowF G C C.output := by
    intro x hx
    change circuitFun n C x = true at hx
    rw [h_eq] at hx
    exact hx
  have h_out_gt_g : n + g < C.output ∧ C.output < n + C.gates.length := by
    have hc := h_cone g hg_lt
    rcases hc.2 with hout | ⟨hnle, hinc⟩
    · exfalso
      apply hg_dirty
      intro x hx
      have : wval C x C.output = true := by rw [hout]; exact hx
      exact h_out_below x this
    · have hlt_len : C.output - n < C.gates.length := inCone_lt_len hinc
      have hgt : g < C.output - n := inCone_lt hinc
      omega
  have h_out_below_gate : BelowF G C (C.output - n) := by
    intro x hx
    apply h_out_below x
    have : n + (C.output - n) = C.output := by omega
    rw [← this]
    exact hx
  have h_dirty_or : ∀ k < C.gates.length, ¬ BelowF G C k → k ≠ g → (gateAt C k).op = GateOp.or := by
    intro k hk hdirty hkg
    rcases hAO.1 _ (gateAt_mem hk) with hop | hop
    · exact (hdirty (h_clean_and k hk hop hkg)).elim
    · exact hop
  have h_dirty_inputs : ∀ k < C.gates.length, ¬ BelowF G C k → ∀ b : Fin 2, ¬ WireBelowF G C (opnd C k b) := by
    intro k hk hdirty b hwb
    rcases hAO.1 _ (gateAt_mem hk) with hop | hop
    · exact h_no_imp k hk hop (opnd C k b) (opnd_mem hAO hk b) hwb
    · apply h_lift
      refine ⟨k, hk, b, h_cone k hk, hop, hdirty, hwb, fun _ => true, ?_⟩
      exact wval_allTrue hAO (opnd C k b) (by have := opnd_lt hAO hk b; omega)
  have h_clean_or_inputs : ∀ k < C.gates.length, BelowF G C k → (gateAt C k).op = GateOp.or →
      ∀ b : Fin 2, n ≤ opnd C k b ∧ opnd C k b - n < k ∧ BelowF G C (opnd C k b - n) := by
    intro k hk hbf hop b
    have hwb : WireBelowF G C (opnd C k b) := by
      intro x hx
      apply hbf x
      change wval C x (n + k) = true
      rw [wval_gate_or hAO x hk hop, Bool.or_eq_true]
      fin_cases b
      · exact Or.inl hx
      · exact Or.inr hx
    have hge : n ≤ opnd C k b := by
      by_contra hlt
      exact not_wireBelowF_input G C (by omega) hwb
    have hlt := opnd_lt hAO hk b
    refine ⟨hge, by omega, ?_⟩
    intro x hx
    apply hwb x
    have : n + (opnd C k b - n) = opnd C k b := by omega
    rw [← this]
    exact hx
  have h_wval_dirty : ∀ w < n + C.gates.length, ¬ WireBelowF G C w → ∀ x : Fin n → Bool,
      wval C x w = true ↔ (usesG n C g w = true ∧ gateVal n C g x = true) ∨ (∃ u ∈ varSet n C g w, x u = true) := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hw hdw x
      by_cases hlt : w < n
      · rw [wval_input C x w hlt, usesG_input n C g w hlt, varSet_input n C g w hlt]
        simp
      · by_cases hwg : w = n + g
        · subst hwg
          rw [usesG_g, varSet_g]
          simp [gateVal, wval]
        · have hk : w - n < C.gates.length := by omega
          have hkg : w - n ≠ g := by omega
          have hwn : w = n + (w - n) := by omega
          have hdk : ¬ BelowF G C (w - n) := by
            intro hbf; apply hdw; rw [hwn]; exact hbf
          have hop : (gateAt C (w - n)).op = GateOp.or := h_dirty_or (w - n) hk hdk hkg
          have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
          have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
          have h0d := h_dirty_inputs (w - n) hk hdk 0
          have h1d := h_dirty_inputs (w - n) hk hdk 1
          have ih0 := ih _ h0lt (by omega) h0d x
          have ih1 := ih _ h1lt (by omega) h1d x
          rw [hwn, wval_gate_or hAO x hk hop, Bool.or_eq_true,
            usesG_gate hAO g (w - n) hk hkg, varSet_gate hAO g (w - n) hk hkg, ih0, ih1]
          simp only [Bool.or_eq_true, Finset.mem_union, or_and_right, exists_or]
          exact or_and_or_iff
  have h_varSet_nonempty : ∀ w < n + C.gates.length, ¬ WireBelowF G C w → usesG n C g w = false →
      (varSet n C g w).Nonempty := by
    intro w hw hdw hug
    have ht := (h_wval_dirty w hw hdw (fun _ => true)).mp (wval_allTrue hAO w hw)
    rw [hug] at ht
    rcases ht with ⟨hfalse, _⟩ | ⟨u, hu, _⟩
    · cases hfalse
    · exact ⟨u, hu⟩
  have h_g_op0_lt : opnd C g 0 < n + g := opnd_lt hAO hg_lt 0
  have h_g_op1_lt : opnd C g 1 < n + g := opnd_lt hAO hg_lt 1
  have h_g_op0_dirty : ¬ WireBelowF G C (opnd C g 0) := h_dirty_inputs g hg_lt hg_dirty 0
  have h_g_op1_dirty : ¬ WireBelowF G C (opnd C g 1) := h_dirty_inputs g hg_lt hg_dirty 1
  have h_g_op0_val : ∀ x, wval C x (opnd C g 0) = true ↔ ∃ u ∈ varSet n C g (opnd C g 0), x u = true := by
    intro x
    have h := h_wval_dirty (opnd C g 0) (by omega) h_g_op0_dirty x
    rw [usesG_lt_g hAO g _ h_g_op0_lt] at h
    simpa using h
  have h_g_op1_val : ∀ x, wval C x (opnd C g 1) = true ↔ ∃ u ∈ varSet n C g (opnd C g 1), x u = true := by
    intro x
    have h := h_wval_dirty (opnd C g 1) (by omega) h_g_op1_dirty x
    rw [usesG_lt_g hAO g _ h_g_op1_lt] at h
    simpa using h
  have h_g_val : ∀ x, gateVal n C g x = true ↔
      (∃ u ∈ varSet n C g (opnd C g 0), x u = true) ∧ (∃ w ∈ varSet n C g (opnd C g 1), x w = true) := by
    intro x
    change wval C x (n + g) = true ↔ _
    rw [wval_gate_and hAO x hg_lt hg_and, Bool.and_eq_true, h_g_op0_val, h_g_op1_val]
  have hv_in_01 : v ∈ varSet n C g (opnd C g 0) ∧ v ∈ varSet n C g (opnd C g 1) := by
    have hv := (h_g_val (unitInput v)).mp hv_g
    rcases hv with ⟨⟨u0, hu0, heq0⟩, ⟨u1, hu1, heq1⟩⟩
    simp only [unitInput, decide_eq_true_eq] at heq0 heq1
    subst heq0; subst heq1
    exact ⟨hu0, hu1⟩
  have h_and_not_both_g : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → a ≠ g →
      ¬ (usesG n C g (opnd C a 0) = true ∧ usesG n C g (opnd C a 1) = true) := by
    intro a ha hop hag ⟨hu0, hu1⟩
    have hbf := h_clean_and a ha hop hag
    have hd0 : ¬ WireBelowF G C (opnd C a 0) := h_no_imp a ha hop _ (opnd_mem hAO ha 0)
    have hd1 : ¬ WireBelowF G C (opnd C a 1) := h_no_imp a ha hop _ (opnd_mem hAO ha 1)
    have h0 : wval C (unitInput v) (opnd C a 0) = true :=
      (h_wval_dirty _ (by have := opnd_lt hAO ha 0; omega) hd0 (unitInput v)).mpr (Or.inl ⟨hu0, hv_g⟩)
    have h1 : wval C (unitInput v) (opnd C a 1) = true :=
      (h_wval_dirty _ (by have := opnd_lt hAO ha 1; omega) hd1 (unitInput v)).mpr (Or.inl ⟨hu1, hv_g⟩)
    have ha_t : gateVal n C a (unitInput v) = true := by
      change wval C (unitInput v) (n + a) = true
      rw [wval_gate_and hAO _ ha hop, h0, h1]; rfl
    have hf := hbf (unitInput v) ha_t
    rw [graphFun_unitInput_false] at hf
    cases hf
  have h_dirty_cone_usesG : ∀ k < C.gates.length, ¬ BelowF G C k → (g = k ∨ InCone n C g k) →
      usesG n C g (n + k) = true := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk hdk hreach
      rcases hreach with hgk | hinc
      · rw [← hgk]; exact usesG_g n C g
      · have hkg : k ≠ g := by have := inCone_lt hinc; omega
        rw [inCone_iff hk] at hinc
        rcases hinc with ⟨w, hwm, hwn, hwlt, hsub⟩
        have hwk : w - n < k := by omega
        have hwn' : w = n + (w - n) := by omega
        have hdw : ¬ BelowF G C (w - n) := by
          intro hbf
          rw [gate_inputs_eq hAO hk] at hwm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
          rcases hwm with rfl | rfl
          · exact h_dirty_inputs k hk hdk 0 (by rw [hwn']; exact hbf)
          · exact h_dirty_inputs k hk hdk 1 (by rw [hwn']; exact hbf)
        have hug := ih (w - n) hwk (by omega) hdw hsub
        rw [usesG_gate hAO g k hk hkg, Bool.or_eq_true]
        rw [gate_inputs_eq hAO hk] at hwm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
        rcases hwm with rfl | rfl
        · exact Or.inl (by rw [hwn']; exact hug)
        · exact Or.inr (by rw [hwn']; exact hug)
  have h_exists_reader : ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ a ≠ g ∧
      (usesG n C g (opnd C a 0) = true ∨ usesG n C g (opnd C a 1) = true) := by
    have hP : ∃ a, a < C.gates.length ∧ (g = a ∨ InCone n C g a) ∧ BelowF G C a := by
      refine ⟨C.output - n, by omega, Or.inr ?_, h_out_below_gate⟩
      have hc := h_cone g hg_lt
      rcases hc.2 with hout | ⟨_, hinc⟩
      · omega
      · exact hinc
    let a := Nat.find hP
    have ha_spec := Nat.find_spec hP
    have ha_min : ∀ k < a, ¬ (k < C.gates.length ∧ (g = k ∨ InCone n C g k) ∧ BelowF G C k) :=
      fun k hk => Nat.find_min hP hk
    rcases ha_spec with ⟨ha_lt, ha_reach, ha_bf⟩
    have hag : a ≠ g := fun heq => hg_dirty (heq ▸ ha_bf)
    have hinc : InCone n C g a := ha_reach.resolve_left hag.symm
    rw [inCone_iff ha_lt] at hinc
    rcases hinc with ⟨w, hwm, hwn, hwlt, hsub⟩
    have hwk : w - n < a := by omega
    have hdw : ¬ BelowF G C (w - n) := fun hbf => ha_min (w - n) hwk ⟨by omega, hsub, hbf⟩
    have hop : (gateAt C a).op = GateOp.and := by
      rcases hAO.1 _ (gateAt_mem ha_lt) with hop | hop
      · exact hop
      · exfalso
        rw [gate_inputs_eq hAO ha_lt] at hwm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
        rcases hwm with rfl | rfl
        · exact hdw (h_clean_or_inputs a ha_lt ha_bf hop 0).2.2
        · exact hdw (h_clean_or_inputs a ha_lt ha_bf hop 1).2.2
    have hug : usesG n C g w = true := by
      have : w = n + (w - n) := by omega
      rw [this]
      exact h_dirty_cone_usesG (w - n) (by omega) hdw hsub
    refine ⟨a, ha_lt, hop, hag, ?_⟩
    rw [gate_inputs_eq hAO ha_lt] at hwm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
    rcases hwm with rfl | rfl
    · exact Or.inl hug
    · exact Or.inr hug
  have h_mem_zSet : ∀ z : Fin n, z ∈ zSet n C g ↔
      ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ a ≠ g ∧
        ((usesG n C g (opnd C a 0) = true ∧ z ∈ varSet n C g (opnd C a 1)) ∨
         (usesG n C g (opnd C a 1) = true ∧ z ∈ varSet n C g (opnd C a 0))) := by
    intro z
    unfold zSet
    simp only [Finset.mem_biUnion, Finset.mem_range]
    constructor
    · rintro ⟨a, ha, hmem⟩
      cases hop : (gateAt C a).op with
      | and =>
        rw [hop] at hmem
        dsimp only at hmem
        by_cases hag : a ≠ g
        · rw [if_pos hag, Finset.mem_union] at hmem
          refine ⟨a, ha, hop, hag, ?_⟩
          rcases hmem with h0 | h1
          · split_ifs at h0 with hu0
            · exact Or.inl ⟨hu0, h0⟩
            · simp at h0
          · split_ifs at h1 with hu1
            · exact Or.inr ⟨hu1, h1⟩
            · simp at h1
        · simp [hag] at hmem
      | or => rw [hop] at hmem; simp at hmem
      | not => rw [hop] at hmem; simp at hmem
      | mod m => rw [hop] at hmem; simp at hmem
      | maj => rw [hop] at hmem; simp at hmem
    · rintro ⟨a, ha, hop, hag, hside⟩
      refine ⟨a, ha, ?_⟩
      rw [hop]
      simp only [hag, ne_eq, not_false_eq_true, ↓reduceIte, Finset.mem_union]
      rcases hside with ⟨hu0, hz1⟩ | ⟨hu1, hz0⟩
      · left; simp [hu0, hz1]
      · right; simp [hu1, hz0]
  have h_zSet_nonempty : (zSet n C g).Nonempty := by
    rcases h_exists_reader with ⟨a, ha, hop, hag, hu0 | hu1⟩
    · have hu1f : usesG n C g (opnd C a 1) = false := by
        cases h : usesG n C g (opnd C a 1)
        · rfl
        · exact (h_and_not_both_g a ha hop hag ⟨hu0, h⟩).elim
      have hd1 : ¬ WireBelowF G C (opnd C a 1) := h_no_imp a ha hop _ (opnd_mem hAO ha 1)
      rcases h_varSet_nonempty (opnd C a 1) (by have := opnd_lt hAO ha 1; omega) hd1 hu1f with ⟨z, hz⟩
      exact ⟨z, (h_mem_zSet z).mpr ⟨a, ha, hop, hag, Or.inl ⟨hu0, hz⟩⟩⟩
    · have hu0f : usesG n C g (opnd C a 0) = false := by
        cases h : usesG n C g (opnd C a 0)
        · rfl
        · exact (h_and_not_both_g a ha hop hag ⟨h, hu1⟩).elim
      have hd0 : ¬ WireBelowF G C (opnd C a 0) := h_no_imp a ha hop _ (opnd_mem hAO ha 0)
      rcases h_varSet_nonempty (opnd C a 0) (by have := opnd_lt hAO ha 0; omega) hd0 hu0f with ⟨z, hz⟩
      exact ⟨z, (h_mem_zSet z).mpr ⟨a, ha, hop, hag, Or.inr ⟨hu1, hz⟩⟩⟩
  have h_zSet_below : ∀ z ∈ zSet n C g, ∀ x : Fin n → Bool,
      gateVal n C g x = true → x z = true → graphFun G ∅ x = true := by
    intro z hz x hgx hxz
    rcases (h_mem_zSet z).mp hz with ⟨a, ha, hop, hag, ⟨hu0, hz1⟩ | ⟨hu1, hz0⟩⟩
    · have hd0 : ¬ WireBelowF G C (opnd C a 0) := h_no_imp a ha hop _ (opnd_mem hAO ha 0)
      have hd1 : ¬ WireBelowF G C (opnd C a 1) := h_no_imp a ha hop _ (opnd_mem hAO ha 1)
      have h0 : wval C x (opnd C a 0) = true :=
        (h_wval_dirty _ (by have := opnd_lt hAO ha 0; omega) hd0 x).mpr (Or.inl ⟨hu0, hgx⟩)
      have h1 : wval C x (opnd C a 1) = true :=
        (h_wval_dirty _ (by have := opnd_lt hAO ha 1; omega) hd1 x).mpr (Or.inr ⟨z, hz1, hxz⟩)
      apply h_clean_and a ha hop hag x
      change wval C x (n + a) = true
      rw [wval_gate_and hAO x ha hop, h0, h1]; rfl
    · have hd0 : ¬ WireBelowF G C (opnd C a 0) := h_no_imp a ha hop _ (opnd_mem hAO ha 0)
      have hd1 : ¬ WireBelowF G C (opnd C a 1) := h_no_imp a ha hop _ (opnd_mem hAO ha 1)
      have h0 : wval C x (opnd C a 0) = true :=
        (h_wval_dirty _ (by have := opnd_lt hAO ha 0; omega) hd0 x).mpr (Or.inr ⟨z, hz0, hxz⟩)
      have h1 : wval C x (opnd C a 1) = true :=
        (h_wval_dirty _ (by have := opnd_lt hAO ha 1; omega) hd1 x).mpr (Or.inl ⟨hu1, hgx⟩)
      apply h_clean_and a ha hop hag x
      change wval C x (n + a) = true
      rw [wval_gate_and hAO x ha hop, h0, h1]; rfl
  have h_zSet_adj_v : ∀ z ∈ zSet n C g, G.Adj v z := by
    intro z hz
    rw [← graphFun_pairInput_iff G v z]
    apply h_zSet_below z hz (pairInput v z)
    · rw [h_g_val]
      exact ⟨⟨v, hv_in_01.1, by simp [pairInput]⟩, ⟨v, hv_in_01.2, by simp [pairInput]⟩⟩
    · simp [pairInput]
  have h_zSet_color : ∀ z ∈ zSet n C g, s z ≠ s v := fun z hz => (h_bip v z (h_zSet_adj_v z hz)).symm
  have h_clean_and_no_two_sided : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → a ≠ g →
      ∀ b : Fin 2, ¬ ((∃ uL ∈ varSet n C g (opnd C a b), s uL = s v) ∧
                      (∃ uR ∈ varSet n C g (opnd C a b), s uR ≠ s v)) := by
    intro a ha hop hag b ⟨⟨uL, huL, hsL⟩, ⟨uR, huR, hsR⟩⟩
    let b' : Fin 2 := if b = 0 then 1 else 0
    have hbf := h_clean_and a ha hop hag
    have hdb : ¬ WireBelowF G C (opnd C a b) := h_no_imp a ha hop _ (opnd_mem hAO ha b)
    have hdb' : ¬ WireBelowF G C (opnd C a b') := h_no_imp a ha hop _ (opnd_mem hAO ha b')
    have h_pair_adj : ∀ x : Fin n → Bool, wval C x (opnd C a b) = true → wval C x (opnd C a b') = true →
        graphFun G ∅ x = true := by
      intro x hx1 hx2
      apply hbf x
      change wval C x (n + a) = true
      rw [wval_gate_and hAO x ha hop, Bool.and_eq_true]
      fin_cases b
      · exact ⟨hx1, hx2⟩
      · exact ⟨hx2, hx1⟩
    cases hub' : usesG n C g (opnd C a b') with
    | true =>
      have h1 : wval C (pairInput v uL) (opnd C a b) = true :=
        (h_wval_dirty _ (by have := opnd_lt hAO ha b; omega) hdb _).mpr
          (Or.inr ⟨uL, huL, by simp [pairInput]⟩)
      have hgv : gateVal n C g (pairInput v uL) = true := by
        rw [h_g_val]
        exact ⟨⟨v, hv_in_01.1, by simp [pairInput]⟩, ⟨v, hv_in_01.2, by simp [pairInput]⟩⟩
      have h2 : wval C (pairInput v uL) (opnd C a b') = true :=
        (h_wval_dirty _ (by have := opnd_lt hAO ha b'; omega) hdb' _).mpr (Or.inl ⟨hub', hgv⟩)
      have hadj : G.Adj v uL := (graphFun_pairInput_iff G v uL).mp (h_pair_adj _ h1 h2)
      exact h_bip v uL hadj hsL.symm
    | false =>
      rcases h_varSet_nonempty (opnd C a b') (by have := opnd_lt hAO ha b'; omega) hdb' hub' with ⟨z, hz⟩
      by_cases hsz : s z = s v
      · have h1 : wval C (pairInput uL z) (opnd C a b) = true :=
          (h_wval_dirty _ (by have := opnd_lt hAO ha b; omega) hdb _).mpr
            (Or.inr ⟨uL, huL, by simp [pairInput]⟩)
        have h2 : wval C (pairInput uL z) (opnd C a b') = true :=
          (h_wval_dirty _ (by have := opnd_lt hAO ha b'; omega) hdb' _).mpr
            (Or.inr ⟨z, hz, by simp [pairInput]⟩)
        have hadj : G.Adj uL z := (graphFun_pairInput_iff G uL z).mp (h_pair_adj _ h1 h2)
        exact h_bip uL z hadj (hsL.trans hsz.symm)
      · have h1 : wval C (pairInput uR z) (opnd C a b) = true :=
          (h_wval_dirty _ (by have := opnd_lt hAO ha b; omega) hdb _).mpr
            (Or.inr ⟨uR, huR, by simp [pairInput]⟩)
        have h2 : wval C (pairInput uR z) (opnd C a b') = true :=
          (h_wval_dirty _ (by have := opnd_lt hAO ha b'; omega) hdb' _).mpr
            (Or.inr ⟨z, hz, by simp [pairInput]⟩)
        have hadj : G.Adj uR z := (graphFun_pairInput_iff G uR z).mp (h_pair_adj _ h1 h2)
        have hsr : s uR = s z := bool_eq_of_ne_ne (Ne.symm hsR) (Ne.symm hsz)
        exact h_bip uR z hadj hsr
  have h_solve_ordered :
      ∀ (aW bW : ℕ),
        aW < n + g → bW < n + g →
        ¬ WireBelowF G C aW → ¬ WireBelowF G C bW →
        (∀ x, gateVal n C g x = (wval C x aW && wval C x bW)) →
        (∀ w ∈ (gateAt C g).inputs, w = aW ∨ w = bW) →
        aW∈(gateAt C g).inputs → bW∈(gateAt C g).inputs →
        (∀ u ∈ varSet n C g aW, s u = s v) →
        ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
          circuitFun n D = graphFun G ∅ ∧
          ∀ k < D.gates.length, (gateAt D k).op = GateOp.and → BelowF G D k := by
    intro aW bW haW_lt hbW_lt haW_d hbW_d hg_ab hg_in haWmem hbWmem hA_L
    set A := varSet n C g aW
    set B := varSet n C g bW
    set Z := zSet n C g
    have haW_val : ∀ x, wval C x aW = true ↔ ∃ u ∈ A, x u = true := by
      intro x
      have h := h_wval_dirty aW (by omega) haW_d x
      rw [usesG_lt_g hAO g aW haW_lt] at h
      simpa using h
    have hbW_val : ∀ x, wval C x bW = true ↔ ∃ w ∈ B, x w = true := by
      intro x
      have h := h_wval_dirty bW (by omega) hbW_d x
      rw [usesG_lt_g hAO g bW hbW_lt] at h
      simpa using h
    have hg_AB : ∀ x, gateVal n C g x = true ↔ (∃ u ∈ A, x u = true) ∧ (∃ w ∈ B, x w = true) := by
      intro x
      rw [hg_ab, Bool.and_eq_true, haW_val, hbW_val]
    have hv_A : v ∈ A := by
      rcases ((hg_AB (unitInput v)).mp hv_g).1 with ⟨u, hu, heq⟩
      simp only [unitInput, decide_eq_true_eq] at heq
      exact heq ▸ hu
    have hv_B : v ∈ B := by
      rcases ((hg_AB (unitInput v)).mp hv_g).2 with ⟨w, hw, heq⟩
      simp only [unitInput, decide_eq_true_eq] at heq
      exact heq ▸ hw
    have h_two_sided_le_b : ∀ k < C.gates.length, ¬ BelowF G C k → k ≠ g →
        (∃ uL ∈ varSet n C g (n + k), s uL = s v) →
        (∃ uR ∈ varSet n C g (n + k), s uR ≠ s v) → n + k ≤ bW := by
      intro k hk hdk hkg hL hR
      have hT : ∃ c, c < C.gates.length ∧ (k = c ∨ InCone n C k c) ∧ (c = g ∨ BelowF G C c) := by
        refine ⟨C.output - n, by omega, Or.inr ?_, Or.inr h_out_below_gate⟩
        have hc := h_cone k hk
        rcases hc.2 with hout | ⟨_, hinc⟩
        · exfalso
          apply hdk
          intro x hx
          exact h_out_below x (by rw [hout]; exact hx)
        · exact hinc
      obtain ⟨c, hc_eq⟩ : ∃ c, c = Nat.find hT := ⟨_, rfl⟩
      have hc_spec : c < C.gates.length ∧ (k = c ∨ InCone n C k c) ∧ (c = g ∨ BelowF G C c) :=
        hc_eq ▸ Nat.find_spec hT
      have hc_min : ∀ j < c, ¬ (j < C.gates.length ∧ (k = j ∨ InCone n C k j) ∧ (j = g ∨ BelowF G C j)) :=
        fun j hj => Nat.find_min hT (hc_eq ▸ hj)
      rcases hc_spec with ⟨hc_lt, hc_reach, hc_end⟩
      have h_sub : ∀ j < c, (k = j ∨ InCone n C k j) → varSet n C g (n + k) ⊆ varSet n C g (n + j) := by
        intro j
        induction j using Nat.strongRecOn with
        | ind j ih =>
          intro hjc hjr
          rcases hjr with hkj | hinc
          · rw [hkj]
          · have hjlt : j < C.gates.length := inCone_lt_len hinc
            have hj_not : ¬ (j = g ∨ BelowF G C j) := fun h => hc_min j hjc ⟨hjlt, Or.inr hinc, h⟩
            have hjg : j ≠ g := fun h => hj_not (Or.inl h)
            rw [inCone_iff hjlt] at hinc
            rcases hinc with ⟨w, hwm, hwn, hwlt, hsub⟩
            have hwn' : w = n + (w - n) := by omega
            have h1 := ih (w - n) (by omega) (by omega) hsub
            rw [varSet_gate hAO g j hjlt hjg]
            rw [gate_inputs_eq hAO hjlt] at hwm
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
            rcases hwm with rfl | rfl
            · exact Finset.Subset.trans h1 (by rw [← hwn']; exact Finset.subset_union_left)
            · exact Finset.Subset.trans h1 (by rw [← hwn']; exact Finset.subset_union_right)
      have hck : k ≠ c := by
        intro heq
        rcases hc_end with hcg | hbf
        · exact hkg (heq.trans hcg)
        · exact hdk (heq ▸ hbf)
      have hc_inc : InCone n C k c := hc_reach.resolve_left hck
      rw [inCone_iff hc_lt] at hc_inc
      rcases hc_inc with ⟨w, hwm, hwn, hwlt, hsub⟩
      have hwn' : w = n + (w - n) := by omega
      have h_k_le : k ≤ w - n := by
        rcases hsub with hkw | hinc'
        · omega
        · have := inCone_lt hinc'; omega
      have h_sub_w : varSet n C g (n + k) ⊆ varSet n C g w := by
        rw [hwn']
        exact h_sub (w - n) (by omega) hsub
      have hwL : ∃ uL ∈ varSet n C g w, s uL = s v := by
        rcases hL with ⟨u, hu, hs⟩; exact ⟨u, h_sub_w hu, hs⟩
      have hwR : ∃ uR ∈ varSet n C g w, s uR ≠ s v := by
        rcases hR with ⟨u, hu, hs⟩; exact ⟨u, h_sub_w hu, hs⟩
      have hdw : ¬ BelowF G C (w - n) := fun hbf =>
        hc_min (w - n) (by omega) ⟨by omega, hsub, Or.inr hbf⟩
      rcases hc_end with hcg | hbf
      · rw [hcg] at hwm
        rcases hg_in w hwm with rfl | rfl
        · rcases hwR with ⟨uR, huR, hsR⟩
          exact (hsR (hA_L uR huR)).elim
        · omega
      · exfalso
        rcases hAO.1 _ (gateAt_mem hc_lt) with hop | hop
        · have hcg : c ≠ g := fun heq => hg_dirty (heq ▸ hbf)
          rw [gate_inputs_eq hAO hc_lt] at hwm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
          rcases hwm with rfl | rfl
          · exact h_clean_and_no_two_sided c hc_lt hop hcg 0 ⟨hwL, hwR⟩
          · exact h_clean_and_no_two_sided c hc_lt hop hcg 1 ⟨hwL, hwR⟩
        · rw [gate_inputs_eq hAO hc_lt] at hwm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
          rcases hwm with rfl | rfl
          · exact hdw (h_clean_or_inputs c hc_lt hbf hop 0).2.2
          · exact hdw (h_clean_or_inputs c hc_lt hbf hop 1).2.2
    have h_del_wval_dirty : ∀ (r : ℕ), r < n + g →
        ∀ w < n + C.gates.length, ¬ WireBelowF G C w → ∀ x : Fin n → Bool,
          wval (delCircuit n C g r) x (delMap n g r w) = true ↔
            (usesG n C g w = true ∧ wval C x r = true) ∨ (∃ u ∈ varSet n C g w, x u = true) := by
      intro r hr
      have hAO' := delCircuit_isAO2 hAO hg_lt hr
      intro w
      induction w using Nat.strongRecOn with
      | ind w ih =>
        intro hw hdw x
        by_cases hlt : w < n + g
        · have hm : delMap n g r w = w := by simp [delMap, hlt]
          rw [hm, delCircuit_wval_lt hAO hg_lt hr x w hlt, h_wval_dirty w hw hdw x, usesG_lt_g hAO g w hlt]
          simp
        · by_cases hwg : w = n + g
          · subst hwg
            have hm : delMap n g r (n + g) = r := by simp [delMap]
            rw [hm, delCircuit_wval_lt hAO hg_lt hr x r hr, usesG_g, varSet_g]
            simp
          · have hk : w - n < C.gates.length := by omega
            have hkg : w - n ≠ g := by omega
            have hwn : w = n + (w - n) := by omega
            have hdk : ¬ BelowF G C (w - n) := fun hbf => hdw (by rw [hwn]; exact hbf)
            have hop : (gateAt C (w - n)).op = GateOp.or := h_dirty_or (w - n) hk hdk hkg
            have hdm : delMap n g r w = n + delGateMap g (w - n) := by
              conv_lhs => rw [hwn]
              exact delMap_gate n g r (w - n) hkg
            have hk' : delGateMap g (w - n) < (delCircuit n C g r).gates.length := by
              rw [delCircuit_len]; unfold delGateMap; split_ifs <;> omega
            have hgate : (gateAt (delCircuit n C g r) (delGateMap g (w - n))).op = GateOp.or := by
              rw [delCircuit_gateAt_src hg_lt hk hkg, hop]
            have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
            have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
            have ih0 := ih _ h0lt (by omega) (h_dirty_inputs (w - n) hk hdk 0) x
            have ih1 := ih _ h1lt (by omega) (h_dirty_inputs (w - n) hk hdk 1) x
            rw [hdm, wval_gate_or hAO' x hk' hgate, Bool.or_eq_true,
              delCircuit_opnd hAO hg_lt hk hkg 0, delCircuit_opnd hAO hg_lt hk hkg 1, ih0, ih1]
            conv_rhs => rw [hwn, usesG_gate hAO g (w - n) hk hkg, varSet_gate hAO g (w - n) hk hkg]
            simp only [Bool.or_eq_true, Finset.mem_union, or_and_right, exists_or]
            exact or_and_or_iff
    have h_solve_Z1_wire : ∀ (m : Fin n) (r : ℕ),
        (∀ z ∈ Z, z = m) → r < n + g →
        (∀ x, gateVal n C g x = true → wval C x r = true) →
        (∀ x, wval C x r = true → x m = true → graphFun G ∅ x = true) →
        ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
          circuitFun n D = graphFun G ∅ ∧
          ∀ k < D.gates.length, (gateAt D k).op = GateOp.and → BelowF G D k := by
      intro m r hZm hr hge_r h_rm_below
      let D := delCircuit n C g r
      have hAO' := delCircuit_isAO2 hAO hg_lt hr
      have h_and_bf : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → a ≠ g →
          BelowF G D (delGateMap g a) := by
        intro a ha hop hag x hDx
        have ha' : delGateMap g a < D.gates.length := by
          rw [delCircuit_len]; unfold delGateMap; split_ifs <;> omega
        have hgate : (gateAt D (delGateMap g a)).op = GateOp.and := by
          rw [delCircuit_gateAt_src hg_lt ha hag, hop]
        change wval D x (n + delGateMap g a) = true at hDx
        rw [wval_gate_and hAO' x ha' hgate, Bool.and_eq_true,
          delCircuit_opnd hAO hg_lt ha hag 0, delCircuit_opnd hAO hg_lt ha hag 1] at hDx
        have hd0 : ¬ WireBelowF G C (opnd C a 0) := h_no_imp a ha hop _ (opnd_mem hAO ha 0)
        have hd1 : ¬ WireBelowF G C (opnd C a 1) := h_no_imp a ha hop _ (opnd_mem hAO ha 1)
        have h0 := (h_del_wval_dirty r hr _ (by have := opnd_lt hAO ha 0; omega) hd0 x).mp hDx.1
        have h1 := (h_del_wval_dirty r hr _ (by have := opnd_lt hAO ha 1; omega) hd1 x).mp hDx.2
        rcases h0 with ⟨hu0, hrx⟩ | ⟨u0, hu0, hxu0⟩
        · have hu1f : usesG n C g (opnd C a 1) = false := by
            cases h : usesG n C g (opnd C a 1)
            · rfl
            · exact (h_and_not_both_g a ha hop hag ⟨hu0, h⟩).elim
          rcases h1 with ⟨hu1t, _⟩ | ⟨z, hz, hxz⟩
          · rw [hu1f] at hu1t; cases hu1t
          · have hzm : z = m := hZm z ((h_mem_zSet z).mpr ⟨a, ha, hop, hag, Or.inl ⟨hu0, hz⟩⟩)
            exact h_rm_below x hrx (hzm ▸ hxz)
        · rcases h1 with ⟨hu1, hrx⟩ | ⟨u1, hu1, hxu1⟩
          · have hzm : u0 = m := hZm u0 ((h_mem_zSet u0).mpr ⟨a, ha, hop, hag, Or.inr ⟨hu1, hu0⟩⟩)
            exact h_rm_below x hrx (hzm ▸ hxu0)
          · apply h_clean_and a ha hop hag x
            change wval C x (n + a) = true
            rw [wval_gate_and hAO x ha hop, Bool.and_eq_true]
            exact ⟨(h_wval_dirty _ (by have := opnd_lt hAO ha 0; omega) hd0 x).mpr (Or.inr ⟨u0, hu0, hxu0⟩),
                   (h_wval_dirty _ (by have := opnd_lt hAO ha 1; omega) hd1 x).mpr (Or.inr ⟨u1, hu1, hxu1⟩)⟩
      have h_all_bf : ∀ k < C.gates.length, BelowF G C k → BelowF G D (delGateMap g k) := by
        intro k
        induction k using Nat.strongRecOn with
        | ind k ih =>
          intro hk hbf
          have hkg : k ≠ g := fun heq => hg_dirty (heq ▸ hbf)
          rcases hAO.1 _ (gateAt_mem hk) with hop | hop
          · exact h_and_bf k hk hop hkg
          · intro x hDx
            have hk' : delGateMap g k < D.gates.length := by
              rw [delCircuit_len]; unfold delGateMap; split_ifs <;> omega
            have hgate : (gateAt D (delGateMap g k)).op = GateOp.or := by
              rw [delCircuit_gateAt_src hg_lt hk hkg, hop]
            change wval D x (n + delGateMap g k) = true at hDx
            rw [wval_gate_or hAO' x hk' hgate, Bool.or_eq_true,
              delCircuit_opnd hAO hg_lt hk hkg 0, delCircuit_opnd hAO hg_lt hk hkg 1] at hDx
            have hi0 := h_clean_or_inputs k hk hbf hop 0
            have hi1 := h_clean_or_inputs k hk hbf hop 1
            have hne0 : opnd C k 0 - n ≠ g := fun heq => hg_dirty (heq ▸ hi0.2.2)
            have hne1 : opnd C k 1 - n ≠ g := fun heq => hg_dirty (heq ▸ hi1.2.2)
            have heq0 : opnd C k 0 = n + (opnd C k 0 - n) := by omega
            have heq1 : opnd C k 1 = n + (opnd C k 1 - n) := by omega
            rcases hDx with h0 | h1
            · rw [heq0, delMap_gate n g r _ hne0] at h0
              exact ih _ hi0.2.1 (by omega) hi0.2.2 x h0
            · rw [heq1, delMap_gate n g r _ hne1] at h1
              exact ih _ hi1.2.1 (by omega) hi1.2.2 x h1
      refine ⟨D, hAO', delCircuit_size_strict n C g r hg_lt, ?_, ?_⟩
      · funext x
        have h_out_ne : C.output - n ≠ g := by omega
        have h_out_eq : C.output = n + (C.output - n) := by omega
        have h_Dout : circuitFun n D x = gateVal n D (delGateMap g (C.output - n)) x := by
          change wval D x (delMap n g r C.output) = wval D x (n + delGateMap g (C.output - n))
          conv_lhs => rw [h_out_eq]
          rw [delMap_gate n g r _ h_out_ne]
        cases hDx : circuitFun n D x with
        | true =>
          rw [h_Dout] at hDx
          exact (h_all_bf (C.output - n) (by omega) h_out_below_gate x hDx).symm
        | false =>
          cases hFx : graphFun G ∅ x with
          | false => rfl
          | true =>
            have hCx : wval C x C.output = true := by
              change circuitFun n C x = true
              rw [h_eq]; exact hFx
            have hDt : circuitFun n D x = true :=
              delCircuit_wval_ge hAO hg_lt hr x (hge_r x) C.output (by omega) hCx
            rw [hDx] at hDt; cases hDt
      · intro k' hk' hop'
        rw [delCircuit_len] at hk'
        let src := if k' < g then k' else k' + 1
        have hsrc_lt : src < C.gates.length := by dsimp [src]; split_ifs <;> omega
        have hsrc_ne : src ≠ g := by dsimp [src]; split_ifs <;> omega
        have hdgm : delGateMap g src = k' := by dsimp [src, delGateMap]; split_ifs <;> omega
        have hop : (gateAt C src).op = GateOp.and := by
          rw [← hdgm, delCircuit_gateAt_src hg_lt hsrc_lt hsrc_ne] at hop'
          exact hop'
        rw [← hdgm]
        exact h_and_bf src hsrc_lt hop hsrc_ne
    by_cases hZ1 : Z.card ≤ 1
    · rcases h_zSet_nonempty with ⟨m, hmZ⟩
      have hZm : ∀ z ∈ Z, z = m := fun z hz => Finset.card_le_one.mp hZ1 z hz m hmZ
      by_cases hAm : ∀ u ∈ A, G.Adj u m
      · apply h_solve_Z1_wire m aW hZm haW_lt
        · intro x hgx; rw [hg_ab, Bool.and_eq_true] at hgx; exact hgx.1
        · intro x hrx hxm
          rcases (haW_val x).mp hrx with ⟨u, hu, hxu⟩
          exact (graphFun_iff x).mpr ⟨u, m, hAm u hu, hxu, hxm⟩
      · push_neg at hAm
        rcases hAm with ⟨u0, hu0A, hu0m⟩
        have hBL_m : ∀ w ∈ B, s w = s v → G.Adj w m := by
          intro w hwB hsw
          have htri : graphFun G ∅ (tripleInput u0 w m) = true := by
            apply h_zSet_below m hmZ (tripleInput u0 w m)
            · rw [hg_AB]
              exact ⟨⟨u0, hu0A, by simp [tripleInput]⟩, ⟨w, hwB, by simp [tripleInput]⟩⟩
            · simp [tripleInput]
          rw [graphFun_tripleInput_iff] at htri
          rcases htri with hadj | hadj | hadj
          · exact (h_bip u0 w hadj ((hA_L u0 hu0A).trans hsw.symm)).elim
          · exact (hu0m hadj).elim
          · exact hadj
        have hm_not_B : m ∉ B := by
          intro hmB
          have hp : graphFun G ∅ (pairInput u0 m) = true := by
            apply h_zSet_below m hmZ (pairInput u0 m)
            · rw [hg_AB]
              exact ⟨⟨u0, hu0A, by simp [pairInput]⟩, ⟨m, hmB, by simp [pairInput]⟩⟩
            · simp [pairInput]
          exact hu0m ((graphFun_pairInput_iff G u0 m).mp hp)
        by_cases hB_L : ∀ w ∈ B, s w = s v
        · apply h_solve_Z1_wire m bW hZm hbW_lt
          · intro x hgx; rw [hg_ab, Bool.and_eq_true] at hgx; exact hgx.2
          · intro x hrx hxm
            rcases (hbW_val x).mp hrx with ⟨w, hw, hxw⟩
            exact (graphFun_iff x).mpr ⟨w, m, hBL_m w hw (hB_L w hw), hxw, hxm⟩
        · push_neg at hB_L
          rcases hB_L with ⟨wR, hwRB, hwRs⟩
          let C1 := restrictTwoSided G C s v g
          have hAO1 : IsAO2 n C1 := restrictTwoSided_isAO2 hAO s v g
          have hg_lt1 : g < C1.gates.length := by rw [restrictTwoSided_len]; exact hg_lt
          let D := delCircuit n C1 g bW
          have hAO' := delCircuit_isAO2 hAO1 hg_lt1 hbW_lt
          have h_no_ts_reads_ts : ∀ k < C.gates.length, k ≠ g →
              ¬ isTwoSided G C s v g (n + k) → ∀ b : Fin 2, ¬ isTwoSided G C s v g (opnd C k b) := by
            intro k hk hkg hnts b hts
            rcases hts with ⟨_, hdw, hL, hR⟩
            by_cases hbf : BelowF G C k
            · rcases hAO.1 _ (gateAt_mem hk) with hop | hop
              · exact h_clean_and_no_two_sided k hk hop hkg b ⟨hL, hR⟩
              · have hi := h_clean_or_inputs k hk hbf hop b
                apply hdw
                have : opnd C k b = n + (opnd C k b - n) := by omega
                rw [this]; exact hi.2.2
            · apply hnts
              refine ⟨by omega, hbf, ?_, ?_⟩
              · rw [varSet_gate hAO g k hk hkg]
                rcases hL with ⟨u, hu, hs⟩
                fin_cases b
                · exact ⟨u, Finset.mem_union_left _ hu, hs⟩
                · exact ⟨u, Finset.mem_union_right _ hu, hs⟩
              · rw [varSet_gate hAO g k hk hkg]
                rcases hR with ⟨u, hu, hs⟩
                fin_cases b
                · exact ⟨u, Finset.mem_union_left _ hu, hs⟩
                · exact ⟨u, Finset.mem_union_right _ hu, hs⟩
          have h_C1_eq_C : ∀ w < n + g, ¬ isTwoSided G C s v g w →
              ∀ x : Fin n → Bool, wval C1 x w = wval C x w := by
            intro w
            induction w using Nat.strongRecOn with
            | ind w ih =>
              intro hw hnts x
              by_cases hlt : w < n
              · rw [wval_input C1 x w hlt, wval_input C x w hlt]
              · have hk : w - n < C.gates.length := by omega
                have hkg : w - n ≠ g := by omega
                have hwn : w = n + (w - n) := by omega
                have hnts' : ¬ isTwoSided G C s v g (n + (w - n)) := by rwa [← hwn]
                have hgt : gateAt C1 (w - n) = gateAt C (w - n) := by
                  rw [restrictTwoSided_gateAt G C s v g (w - n) hk]
                  split_ifs with hcond
                  · exfalso; exact hnts' ⟨by omega, hcond.1, hcond.2.1, hcond.2.2⟩
                  · rfl
                have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
                have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
                have h0nts := h_no_ts_reads_ts (w - n) hk hkg hnts' 0
                have h1nts := h_no_ts_reads_ts (w - n) hk hkg hnts' 1
                have hop0 : opnd C1 (w - n) 0 = opnd C (w - n) 0 := by unfold opnd; rw [hgt]
                have hop1 : opnd C1 (w - n) 1 = opnd C (w - n) 1 := by unfold opnd; rw [hgt]
                have hk1 : w - n < C1.gates.length := by rw [restrictTwoSided_len]; exact hk
                rw [hwn]
                rcases hAO.1 _ (gateAt_mem hk) with hop | hop
                · rw [wval_gate_and hAO1 x hk1 (by rw [hgt]; exact hop), wval_gate_and hAO x hk hop,
                    hop0, hop1, ih _ h0lt (by omega) h0nts x, ih _ h1lt (by omega) h1nts x]
                · rw [wval_gate_or hAO1 x hk1 (by rw [hgt]; exact hop), wval_gate_or hAO x hk hop,
                    hop0, hop1, ih _ h0lt (by omega) h0nts x, ih _ h1lt (by omega) h1nts x]
          have h_C1_ts_bounds : ∀ w < n + g, isTwoSided G C s v g w → ∀ x : Fin n → Bool,
              (wval C1 x w = true → x v = true ∨ ∃ u ∈ varSet n C g w, s u = s v ∧ x u = true) ∧
              ((∃ u ∈ varSet n C g w, s u = s v ∧ x u = true) → wval C1 x w = true) := by
            intro w
            induction w using Nat.strongRecOn with
            | ind w ih =>
              intro hw hts x
              have hge_n : n ≤ w := by
                by_contra hlt
                rcases hts with ⟨_, _, ⟨uL, huL, hsL⟩, ⟨uR, huR, hsR⟩⟩
                rw [varSet_input n C g w (by omega)] at huL huR
                simp only [Finset.mem_singleton] at huL huR
                subst huL; subst huR
                exact hsR hsL
              have hk : w - n < C.gates.length := by omega
              have hkg : w - n ≠ g := by omega
              have hwn : w = n + (w - n) := by omega
              have hdk : ¬ BelowF G C (w - n) := fun hbf => hts.2.1 (by rw [hwn]; exact hbf)
              have hop : (gateAt C (w - n)).op = GateOp.or := h_dirty_or (w - n) hk hdk hkg
              have hk1 : w - n < C1.gates.length := by rw [restrictTwoSided_len]; exact hk
              have hgt : gateAt C1 (w - n) = ⟨GateOp.or, (gateAt C (w - n)).inputs.map (restrictMap C s v g)⟩ := by
                rw [restrictTwoSided_gateAt G C s v g (w - n) hk]
                have hcond : ¬ BelowF G C (w - n) ∧ (∃ u ∈ varSet n C g (n + (w - n)), s u = s v) ∧
                    (∃ u ∈ varSet n C g (n + (w - n)), s u ≠ s v) := by
                  rw [← hwn]; exact ⟨hdk, hts.2.2.1, hts.2.2.2⟩
                simp [hcond, hop]
              have hop_eq : (gateAt C1 (w - n)).op = GateOp.or := by rw [hgt]
              have hop0 : opnd C1 (w - n) 0 = restrictMap C s v g (opnd C (w - n) 0) := by
                unfold opnd; rw [hgt, gate_inputs_eq hAO hk]; rfl
              have hop1 : opnd C1 (w - n) 1 = restrictMap C s v g (opnd C (w - n) 1) := by
                unfold opnd; rw [hgt, gate_inputs_eq hAO hk]; rfl
              have h_branch : ∀ b : Fin 2,
                  (wval C1 x (restrictMap C s v g (opnd C (w - n) b)) = true →
                    x v = true ∨ ∃ u ∈ varSet n C g (opnd C (w - n) b), s u = s v ∧ x u = true) ∧
                  ((∃ u ∈ varSet n C g (opnd C (w - n) b), s u = s v ∧ x u = true) →
                    wval C1 x (restrictMap C s v g (opnd C (w - n) b)) = true) := by
                intro b
                set uW := opnd C (w - n) b
                have huW_lt : uW < w := by have := opnd_lt hAO hk b; omega
                have huW_d : ¬ WireBelowF G C uW := h_dirty_inputs (w - n) hk hdk b
                have huW_val : wval C x uW = true ↔ ∃ u ∈ varSet n C g uW, x u = true := by
                  have h := h_wval_dirty uW (by omega) huW_d x
                  rw [usesG_lt_g hAO g uW (by omega)] at h
                  simpa using h
                unfold restrictMap
                by_cases hR : ∀ u ∈ varSet n C g uW, s u ≠ s v
                · rw [ite_eq_left_iff.mpr (fun hn => (hn hR).elim)]
                  constructor
                  · intro hv1; rw [wval_input C1 x v.val v.isLt] at hv1; exact Or.inl hv1
                  · rintro ⟨u, hu, hsu, _⟩; exact (hR u hu hsu).elim
                · rw [ite_eq_right_iff.mpr (fun hy => (hR hy).elim)]
                  push_neg at hR
                  rcases hR with ⟨uL, huL, hsL⟩
                  by_cases hR2 : ∃ uR ∈ varSet n C g uW, s uR ≠ s v
                  · exact ih uW huW_lt (by omega) ⟨by omega, huW_d, ⟨uL, huL, hsL⟩, hR2⟩ x
                  · push_neg at hR2
                    have hnts_u : ¬ isTwoSided G C s v g uW := by
                      rintro ⟨_, _, _, ⟨uR, huR, hsR⟩⟩; exact hsR (hR2 uR huR)
                    rw [h_C1_eq_C uW (by omega) hnts_u x, huW_val]
                    constructor
                    · rintro ⟨u, hu, hxu⟩; exact Or.inr ⟨u, hu, hR2 u hu, hxu⟩
                    · rintro ⟨u, hu, _, hxu⟩; exact ⟨u, hu, hxu⟩
              have hb0 := h_branch 0
              have hb1 := h_branch 1
              rw [hwn, wval_gate_or hAO1 x hk1 hop_eq, Bool.or_eq_true, hop0, hop1,
                varSet_gate hAO g (w - n) hk hkg]
              constructor
              · rintro (h0 | h1)
                · rcases hb0.1 h0 with hv1 | ⟨u, hu, hsu, hxu⟩
                  · exact Or.inl hv1
                  · exact Or.inr ⟨u, Finset.mem_union_left _ hu, hsu, hxu⟩
                · rcases hb1.1 h1 with hv1 | ⟨u, hu, hsu, hxu⟩
                  · exact Or.inl hv1
                  · exact Or.inr ⟨u, Finset.mem_union_right _ hu, hsu, hxu⟩
              · rintro ⟨u, hu, hsu, hxu⟩
                rcases Finset.mem_union.mp hu with hu0 | hu1
                · exact Or.inl (hb0.2 ⟨u, hu0, hsu, hxu⟩)
                · exact Or.inr (hb1.2 ⟨u, hu1, hsu, hxu⟩)
          have h_C1_bW : ∀ x : Fin n → Bool, wval C1 x bW = true ↔ ∃ w ∈ B, s w = s v ∧ x w = true := by
            intro x
            have hts_b : isTwoSided G C s v g bW := ⟨by omega, hbW_d, ⟨v, hv_B, rfl⟩, ⟨wR, hwRB, hwRs⟩⟩
            have hb := h_C1_ts_bounds bW hbW_lt hts_b x
            constructor
            · intro h1
              rcases hb.1 h1 with hv1 | h2
              · exact ⟨v, hv_B, rfl, hv1⟩
              · exact h2
            · exact hb.2
          have h_D_dirty : ∀ w < n + C.gates.length, ¬ WireBelowF G C w → ¬ isTwoSided G C s v g w →
              ∀ x : Fin n → Bool,
                wval D x (delMap n g bW w) = true ↔
                  (usesG n C g w = true ∧ wval C1 x bW = true) ∨ (∃ u ∈ varSet n C g w, x u = true) := by
            intro w
            induction w using Nat.strongRecOn with
            | ind w ih =>
              intro hw hdw hnts x
              by_cases hlt : w < n + g
              · have hm : delMap n g bW w = w := by simp [delMap, hlt]
                rw [hm, delCircuit_wval_lt hAO1 hg_lt1 hbW_lt x w hlt, h_C1_eq_C w hlt hnts x,
                  h_wval_dirty w hw hdw x, usesG_lt_g hAO g w hlt]
                simp
              · by_cases hwg : w = n + g
                · subst hwg
                  have hm : delMap n g bW (n + g) = bW := by simp [delMap]
                  rw [hm, delCircuit_wval_lt hAO1 hg_lt1 hbW_lt x bW hbW_lt, usesG_g, varSet_g]
                  simp
                · have hk : w - n < C.gates.length := by omega
                  have hkg : w - n ≠ g := by omega
                  have hwn : w = n + (w - n) := by omega
                  have hdk : ¬ BelowF G C (w - n) := fun hbf => hdw (by rw [hwn]; exact hbf)
                  have hop : (gateAt C (w - n)).op = GateOp.or := h_dirty_or (w - n) hk hdk hkg
                  have hnts' : ¬ isTwoSided G C s v g (n + (w - n)) := by rwa [← hwn]
                  have hgt1 : gateAt C1 (w - n) = gateAt C (w - n) := by
                    rw [restrictTwoSided_gateAt G C s v g (w - n) hk]
                    split_ifs with hcond
                    · exfalso; exact hnts' ⟨by omega, hcond.1, hcond.2.1, hcond.2.2⟩
                    · rfl
                  have hdm : delMap n g bW w = n + delGateMap g (w - n) := by
                    conv_lhs => rw [hwn]
                    exact delMap_gate n g bW (w - n) hkg
                  have hk1 : w - n < C1.gates.length := by rw [restrictTwoSided_len]; exact hk
                  have hk' : delGateMap g (w - n) < D.gates.length := by
                    rw [delCircuit_len, restrictTwoSided_len]; unfold delGateMap; split_ifs <;> omega
                  have hgate : (gateAt D (delGateMap g (w - n))).op = GateOp.or := by
                    rw [delCircuit_gateAt_src hg_lt1 hk1 hkg, hgt1, hop]
                  have hop0 : opnd D (delGateMap g (w - n)) 0 = delMap n g bW (opnd C (w - n) 0) := by
                    rw [delCircuit_opnd hAO1 hg_lt1 hk1 hkg 0]; unfold opnd; rw [hgt1]
                  have hop1 : opnd D (delGateMap g (w - n)) 1 = delMap n g bW (opnd C (w - n) 1) := by
                    rw [delCircuit_opnd hAO1 hg_lt1 hk1 hkg 1]; unfold opnd; rw [hgt1]
                  have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
                  have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
                  have ih0 := ih _ h0lt (by omega) (h_dirty_inputs (w - n) hk hdk 0)
                    (h_no_ts_reads_ts (w - n) hk hkg hnts' 0) x
                  have ih1 := ih _ h1lt (by omega) (h_dirty_inputs (w - n) hk hdk 1)
                    (h_no_ts_reads_ts (w - n) hk hkg hnts' 1) x
                  rw [hdm, wval_gate_or hAO' x hk' hgate, Bool.or_eq_true, hop0, hop1, ih0, ih1]
                  conv_rhs => rw [hwn, usesG_gate hAO g (w - n) hk hkg, varSet_gate hAO g (w - n) hk hkg]
                  simp only [Bool.or_eq_true, Finset.mem_union, or_and_right, exists_or]
                  exact or_and_or_iff
          have h_C1_clean : ∀ k < C.gates.length, BelowF G C k → gateAt C1 k = gateAt C k := by
            intro k hk hbf
            rw [restrictTwoSided_gateAt G C s v g k hk]
            simp [hbf]
          have h_and_bf : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → a ≠ g →
              BelowF G D (delGateMap g a) := by
            intro a ha hop hag x hDx
            have ha1 : a < C1.gates.length := by rw [restrictTwoSided_len]; exact ha
            have ha' : delGateMap g a < D.gates.length := by
              rw [delCircuit_len, restrictTwoSided_len]; unfold delGateMap; split_ifs <;> omega
            have hgt1 := h_C1_clean a ha (h_clean_and a ha hop hag)
            have hgate : (gateAt D (delGateMap g a)).op = GateOp.and := by
              rw [delCircuit_gateAt_src hg_lt1 ha1 hag, hgt1, hop]
            have hop0 : opnd D (delGateMap g a) 0 = delMap n g bW (opnd C a 0) := by
              rw [delCircuit_opnd hAO1 hg_lt1 ha1 hag 0]; unfold opnd; rw [hgt1]
            have hop1 : opnd D (delGateMap g a) 1 = delMap n g bW (opnd C a 1) := by
              rw [delCircuit_opnd hAO1 hg_lt1 ha1 hag 1]; unfold opnd; rw [hgt1]
            change wval D x (n + delGateMap g a) = true at hDx
            rw [wval_gate_and hAO' x ha' hgate, Bool.and_eq_true, hop0, hop1] at hDx
            have hd0 : ¬ WireBelowF G C (opnd C a 0) := h_no_imp a ha hop _ (opnd_mem hAO ha 0)
            have hd1 : ¬ WireBelowF G C (opnd C a 1) := h_no_imp a ha hop _ (opnd_mem hAO ha 1)
            have hnts_a : ¬ isTwoSided G C s v g (n + a) := fun h => h.2.1 (h_clean_and a ha hop hag)
            have h0 := (h_D_dirty _ (by have := opnd_lt hAO ha 0; omega) hd0
              (h_no_ts_reads_ts a ha hag hnts_a 0) x).mp hDx.1
            have h1 := (h_D_dirty _ (by have := opnd_lt hAO ha 1; omega) hd1
              (h_no_ts_reads_ts a ha hag hnts_a 1) x).mp hDx.2
            rcases h0 with ⟨hu0, hbx⟩ | ⟨u0, hu0, hxu0⟩
            · have hu1f : usesG n C g (opnd C a 1) = false := by
                cases h : usesG n C g (opnd C a 1)
                · rfl
                · exact (h_and_not_both_g a ha hop hag ⟨hu0, h⟩).elim
              rcases h1 with ⟨hu1t, _⟩ | ⟨z, hz, hxz⟩
              · rw [hu1f] at hu1t; cases hu1t
              · have hzm : z = m := hZm z ((h_mem_zSet z).mpr ⟨a, ha, hop, hag, Or.inl ⟨hu0, hz⟩⟩)
                rcases (h_C1_bW x).mp hbx with ⟨w, hwB, hsw, hxw⟩
                exact (graphFun_iff x).mpr ⟨w, m, hBL_m w hwB hsw, hxw, hzm ▸ hxz⟩
            · rcases h1 with ⟨hu1, hbx⟩ | ⟨u1, hu1, hxu1⟩
              · have hzm : u0 = m := hZm u0 ((h_mem_zSet u0).mpr ⟨a, ha, hop, hag, Or.inr ⟨hu1, hu0⟩⟩)
                rcases (h_C1_bW x).mp hbx with ⟨w, hwB, hsw, hxw⟩
                exact (graphFun_iff x).mpr ⟨w, m, hBL_m w hwB hsw, hxw, hzm ▸ hxu0⟩
              · apply h_clean_and a ha hop hag x
                change wval C x (n + a) = true
                rw [wval_gate_and hAO x ha hop, Bool.and_eq_true]
                exact ⟨(h_wval_dirty _ (by have := opnd_lt hAO ha 0; omega) hd0 x).mpr (Or.inr ⟨u0, hu0, hxu0⟩),
                       (h_wval_dirty _ (by have := opnd_lt hAO ha 1; omega) hd1 x).mpr (Or.inr ⟨u1, hu1, hxu1⟩)⟩
          have h_all_bf : ∀ k < C.gates.length, BelowF G C k → BelowF G D (delGateMap g k) := by
            intro k
            induction k using Nat.strongRecOn with
            | ind k ih =>
              intro hk hbf
              have hkg : k ≠ g := fun heq => hg_dirty (heq ▸ hbf)
              rcases hAO.1 _ (gateAt_mem hk) with hop | hop
              · exact h_and_bf k hk hop hkg
              · intro x hDx
                have hk1 : k < C1.gates.length := by rw [restrictTwoSided_len]; exact hk
                have hk' : delGateMap g k < D.gates.length := by
                  rw [delCircuit_len, restrictTwoSided_len]; unfold delGateMap; split_ifs <;> omega
                have hgt1 := h_C1_clean k hk hbf
                have hgate : (gateAt D (delGateMap g k)).op = GateOp.or := by
                  rw [delCircuit_gateAt_src hg_lt1 hk1 hkg, hgt1, hop]
                have hop0 : opnd D (delGateMap g k) 0 = delMap n g bW (opnd C k 0) := by
                  rw [delCircuit_opnd hAO1 hg_lt1 hk1 hkg 0]; unfold opnd; rw [hgt1]
                have hop1 : opnd D (delGateMap g k) 1 = delMap n g bW (opnd C k 1) := by
                  rw [delCircuit_opnd hAO1 hg_lt1 hk1 hkg 1]; unfold opnd; rw [hgt1]
                change wval D x (n + delGateMap g k) = true at hDx
                rw [wval_gate_or hAO' x hk' hgate, Bool.or_eq_true, hop0, hop1] at hDx
                have hi0 := h_clean_or_inputs k hk hbf hop 0
                have hi1 := h_clean_or_inputs k hk hbf hop 1
                have hne0 : opnd C k 0 - n ≠ g := fun heq => hg_dirty (heq ▸ hi0.2.2)
                have hne1 : opnd C k 1 - n ≠ g := fun heq => hg_dirty (heq ▸ hi1.2.2)
                have heq0 : opnd C k 0 = n + (opnd C k 0 - n) := by omega
                have heq1 : opnd C k 1 = n + (opnd C k 1 - n) := by omega
                rcases hDx with h0 | h1
                · rw [heq0, delMap_gate n g bW _ hne0] at h0
                  exact ih _ hi0.2.1 (by omega) hi0.2.2 x h0
                · rw [heq1, delMap_gate n g bW _ hne1] at h1
                  exact ih _ hi1.2.1 (by omega) hi1.2.2 x h1
          have h_edge_keep : ∀ p q : Fin n, G.Adj p q → s p = s v →
              ∀ k < C.gates.length, BelowF G C k →
                gateVal n C k (pairInput p q) = true → gateVal n D (delGateMap g k) (pairInput p q) = true := by
            intro p q hpq hsp k
            have hsq : s q ≠ s v := fun heq => h_bip p q hpq (hsp.trans heq.symm)
            induction k using Nat.strongRecOn with
            | ind k ih =>
              intro hk hbf hCk
              have hkg : k ≠ g := fun heq => hg_dirty (heq ▸ hbf)
              have hk1 : k < C1.gates.length := by rw [restrictTwoSided_len]; exact hk
              have hk' : delGateMap g k < D.gates.length := by
                rw [delCircuit_len, restrictTwoSided_len]; unfold delGateMap; split_ifs <;> omega
              have hgt1 := h_C1_clean k hk hbf
              have hop0 : opnd D (delGateMap g k) 0 = delMap n g bW (opnd C k 0) := by
                rw [delCircuit_opnd hAO1 hg_lt1 hk1 hkg 0]; unfold opnd; rw [hgt1]
              have hop1 : opnd D (delGateMap g k) 1 = delMap n g bW (opnd C k 1) := by
                rw [delCircuit_opnd hAO1 hg_lt1 hk1 hkg 1]; unfold opnd; rw [hgt1]
              rcases hAO.1 _ (gateAt_mem hk) with hop | hop
              · have hgate : (gateAt D (delGateMap g k)).op = GateOp.and := by
                  rw [delCircuit_gateAt_src hg_lt1 hk1 hkg, hgt1, hop]
                change wval C (pairInput p q) (n + k) = true at hCk
                rw [wval_gate_and hAO _ hk hop, Bool.and_eq_true] at hCk
                change wval D (pairInput p q) (n + delGateMap g k) = true
                rw [wval_gate_and hAO' _ hk' hgate, Bool.and_eq_true, hop0, hop1]
                have hd0 : ¬ WireBelowF G C (opnd C k 0) := h_no_imp k hk hop _ (opnd_mem hAO hk 0)
                have hd1 : ¬ WireBelowF G C (opnd C k 1) := h_no_imp k hk hop _ (opnd_mem hAO hk 1)
                have hnts_k : ¬ isTwoSided G C s v g (n + k) := fun h => h.2.1 hbf
                have h0 := (h_wval_dirty _ (by have := opnd_lt hAO hk 0; omega) hd0 _).mp hCk.1
                have h1 := (h_wval_dirty _ (by have := opnd_lt hAO hk 1; omega) hd1 _).mp hCk.2
                have h_g_to_b : (∃ z ∈ Z, pairInput p q z = true) →
                    gateVal n C g (pairInput p q) = true → wval C1 (pairInput p q) bW = true := by
                  rintro ⟨z, hzZ, hpqz⟩ hgx
                  have hzm : z = m := hZm z hzZ
                  rw [hzm] at hpqz
                  simp only [pairInput, decide_eq_true_eq] at hpqz
                  have hqm : q = m := by
                    rcases hpqz with hmp | hmq
                    · exact (h_zSet_color m hmZ (hmp ▸ hsp)).elim
                    · exact hmq.symm
                  rw [hqm] at hgx ⊢
                  rcases ((hg_AB (pairInput p m)).mp hgx).2 with ⟨w, hwB, hpqw⟩
                  simp only [pairInput, decide_eq_true_eq] at hpqw
                  rcases hpqw with hwp | hwm
                  · exact (h_C1_bW (pairInput p m)).mpr ⟨w, hwB, hwp ▸ hsp, by simp [pairInput, hwp]⟩
                  · exact (hm_not_B (hwm ▸ hwB)).elim
                rw [h_D_dirty _ (by have := opnd_lt hAO hk 0; omega) hd0 (h_no_ts_reads_ts k hk hkg hnts_k 0),
                  h_D_dirty _ (by have := opnd_lt hAO hk 1; omega) hd1 (h_no_ts_reads_ts k hk hkg hnts_k 1)]
                rcases h0 with ⟨hu0, hgx⟩ | h0s
                · have hu1f : usesG n C g (opnd C k 1) = false := by
                    cases h : usesG n C g (opnd C k 1)
                    · rfl
                    · exact (h_and_not_both_g k hk hop hkg ⟨hu0, h⟩).elim
                  rcases h1 with ⟨hu1t, _⟩ | ⟨z, hz, hpqz⟩
                  · rw [hu1f] at hu1t; cases hu1t
                  · have hzZ : z ∈ Z := (h_mem_zSet z).mpr ⟨k, hk, hop, hkg, Or.inl ⟨hu0, hz⟩⟩
                    exact ⟨Or.inl ⟨hu0, h_g_to_b ⟨z, hzZ, hpqz⟩ hgx⟩, Or.inr ⟨z, hz, hpqz⟩⟩
                · rcases h1 with ⟨hu1, hgx⟩ | h1s
                  · rcases h0s with ⟨z, hz, hpqz⟩
                    have hzZ : z ∈ Z := (h_mem_zSet z).mpr ⟨k, hk, hop, hkg, Or.inr ⟨hu1, hz⟩⟩
                    exact ⟨Or.inr ⟨z, hz, hpqz⟩, Or.inl ⟨hu1, h_g_to_b ⟨z, hzZ, hpqz⟩ hgx⟩⟩
                  · exact ⟨Or.inr h0s, Or.inr h1s⟩
              · have hgate : (gateAt D (delGateMap g k)).op = GateOp.or := by
                  rw [delCircuit_gateAt_src hg_lt1 hk1 hkg, hgt1, hop]
                change wval C (pairInput p q) (n + k) = true at hCk
                rw [wval_gate_or hAO _ hk hop, Bool.or_eq_true] at hCk
                change wval D (pairInput p q) (n + delGateMap g k) = true
                rw [wval_gate_or hAO' _ hk' hgate, Bool.or_eq_true, hop0, hop1]
                have hi0 := h_clean_or_inputs k hk hbf hop 0
                have hi1 := h_clean_or_inputs k hk hbf hop 1
                have hne0 : opnd C k 0 - n ≠ g := fun heq => hg_dirty (heq ▸ hi0.2.2)
                have hne1 : opnd C k 1 - n ≠ g := fun heq => hg_dirty (heq ▸ hi1.2.2)
                have heq0 : opnd C k 0 = n + (opnd C k 0 - n) := by omega
                have heq1 : opnd C k 1 = n + (opnd C k 1 - n) := by omega
                rcases hCk with h0 | h1
                · left
                  rw [heq0, delMap_gate n g bW _ hne0]
                  exact ih _ hi0.2.1 (by omega) hi0.2.2
                    (by change wval C (pairInput p q) (n + (opnd C k 0 - n)) = true; rw [← heq0]; exact h0)
                · right
                  rw [heq1, delMap_gate n g bW _ hne1]
                  exact ih _ hi1.2.1 (by omega) hi1.2.2
                    (by change wval C (pairInput p q) (n + (opnd C k 1 - n)) = true; rw [← heq1]; exact h1)
          have h_Dout : ∀ x, circuitFun n D x = gateVal n D (delGateMap g (C.output - n)) x := by
            intro x
            change wval D x (delMap n g bW C.output) = wval D x (n + delGateMap g (C.output - n))
            have h_out_ne : C.output - n ≠ g := by omega
            have h_out_eq : C.output = n + (C.output - n) := by omega
            conv_lhs => rw [h_out_eq]
            rw [delMap_gate n g bW _ h_out_ne]
          refine ⟨D, hAO', by rw [Circuit.size, delCircuit_len, restrictTwoSided_len]; change C.gates.length-1<C.gates.length; omega, ?_, ?_⟩
          · apply circuitFun_eq_graphFun_of hAO'
            · intro x hx
              rw [h_Dout] at hx
              exact h_all_bf (C.output - n) (by omega) h_out_below_gate x hx
            · intro p q hpq
              have hCpq : gateVal n C (C.output - n) (pairInput p q) = true := by
                have h1 : circuitFun n C (pairInput p q) = true := by
                  rw [h_eq]; exact (graphFun_pairInput_iff G p q).mpr hpq
                change wval C (pairInput p q) C.output = true at h1
                have : C.output = n + (C.output - n) := by omega
                rw [this] at h1; exact h1
              by_cases hsp : s p = s v
              · rw [h_Dout]
                exact h_edge_keep p q hpq hsp (C.output - n) (by omega) h_out_below_gate hCpq
              · have hsq : s q = s v := bool_eq_of_ne_ne (h_bip p q hpq) hsp
                have hsym : pairInput p q = pairInput q p := by
                  funext t; simp [pairInput, or_comm]
                rw [hsym, h_Dout]
                exact h_edge_keep q p hpq.symm hsq (C.output - n) (by omega) h_out_below_gate (hsym ▸ hCpq)
          · intro k' hk' hop'
            rw [delCircuit_len, restrictTwoSided_len] at hk'
            let src := if k' < g then k' else k' + 1
            have hsrc_lt : src < C.gates.length := by dsimp [src]; split_ifs <;> omega
            have hsrc_ne : src ≠ g := by dsimp [src]; split_ifs <;> omega
            have hsrc1 : src < C1.gates.length := by rw [restrictTwoSided_len]; exact hsrc_lt
            have hdgm : delGateMap g src = k' := by dsimp [src, delGateMap]; split_ifs <;> omega
            have hop1 : (gateAt C1 src).op = GateOp.and := by
              rw [← hdgm, delCircuit_gateAt_src hg_lt1 hsrc1 hsrc_ne] at hop'
              exact hop'
            have hop : (gateAt C src).op = GateOp.and := by
              rw [restrictTwoSided_gateAt G C s v g src hsrc_lt] at hop1
              split_ifs at hop1 <;> exact hop1
            rw [← hdgm]
            exact h_and_bf src hsrc_lt hop hsrc_ne
    · have hZ2 : 1 < Z.card := by omega
      have hAB_inter : ∀ u ∈ A, u ∈ B → u = v := by
        intro u huA huB
        by_contra huv
        rcases Finset.one_lt_card.mp hZ2 with ⟨z1, hz1, z2, hz2, hz12⟩
        have hadj_u : ∀ z ∈ Z, G.Adj u z := by
          intro z hz
          rw [← graphFun_pairInput_iff G u z]
          apply h_zSet_below z hz (pairInput u z)
          · rw [hg_AB]
            exact ⟨⟨u, huA, by simp [pairInput]⟩, ⟨u, huB, by simp [pairInput]⟩⟩
          · simp [pairInput]
        exact hz12 (noFourCycle_unique h_c4 huv (hadj_u z1 hz1) (h_zSet_adj_v z1 hz1)
          (hadj_u z2 hz2) (h_zSet_adj_v z2 hz2))
      by_cases hBZ : ∃ m ∈ B, m ∈ Z
      · rcases hBZ with ⟨m, hmB, hmZ⟩
        by_cases hA_only_v : ∀ u ∈ A, u = v
        · let D := delCircuit n C g v.val
          have hvl : v.val < n + g := by omega
          have hAO' := delCircuit_isAO2 hAO hg_lt hvl
          have hg_eq_v : ∀ x, gateVal n C g x = true ↔ wval C x v.val = true := by
            intro x
            rw [hg_AB, wval_input C x v.val v.isLt]
            constructor
            · rintro ⟨⟨u, huA, hxu⟩, _⟩
              rw [hA_only_v u huA] at hxu; exact hxu
            · intro hxv
              exact ⟨⟨v, hv_A, hxv⟩, ⟨v, hv_B, hxv⟩⟩
          refine ⟨D, hAO', delCircuit_size_strict n C g v.val hg_lt, ?_, ?_⟩
          · funext x
            have hle_out := delCircuit_wval_le hAO hg_lt hvl x (hg_eq_v x).mpr C.output (by omega)
            have hge_out := delCircuit_wval_ge hAO hg_lt hvl x (hg_eq_v x).mp C.output (by omega)
            cases hDx : circuitFun n D x with
            | true =>
              have hCx : circuitFun n C x = true := hle_out hDx
              rw [h_eq] at hCx; exact hCx.symm
            | false =>
              cases hFx : graphFun G ∅ x with
              | false => rfl
              | true =>
                have hCx : circuitFun n C x = true := by rw [h_eq]; exact hFx
                have hDt : circuitFun n D x = true := hge_out hCx
                rw [hDx] at hDt; cases hDt
          · intro k' hk' hop' x hDx
            rw [delCircuit_len] at hk'
            let src := if k' < g then k' else k' + 1
            have hsrc_lt : src < C.gates.length := by dsimp [src]; split_ifs <;> omega
            have hsrc_ne : src ≠ g := by dsimp [src]; split_ifs <;> omega
            have hdgm : delGateMap g src = k' := by dsimp [src, delGateMap]; split_ifs <;> omega
            have hop : (gateAt C src).op = GateOp.and := by
              rw [← hdgm, delCircuit_gateAt_src hg_lt hsrc_lt hsrc_ne] at hop'
              exact hop'
            apply h_clean_and src hsrc_lt hop hsrc_ne x
            apply delCircuit_wval_le hAO hg_lt hvl x (hg_eq_v x).mpr (n + src) (by omega)
            rw [delMap_gate n g v.val src hsrc_ne, hdgm]
            exact hDx
        · push_neg at hA_only_v
          rcases hA_only_v with ⟨u0, hu0A, hu0v⟩
          have hAm : ∀ u ∈ A, G.Adj u m := by
            intro u huA
            rw [← graphFun_pairInput_iff G u m]
            apply h_zSet_below m hmZ (pairInput u m)
            · rw [hg_AB]
              exact ⟨⟨u, huA, by simp [pairInput]⟩, ⟨m, hmB, by simp [pairInput]⟩⟩
            · simp [pairInput]
          have hBZ_uniq : ∀ m' ∈ B, m' ∈ Z → m' = m := by
            intro m' hm'B hm'Z
            have hu0m' : G.Adj u0 m' := by
              rw [← graphFun_pairInput_iff G u0 m']
              apply h_zSet_below m' hm'Z (pairInput u0 m')
              · rw [hg_AB]
                exact ⟨⟨u0, hu0A, by simp [pairInput]⟩, ⟨m', hm'B, by simp [pairInput]⟩⟩
              · simp [pairInput]
            exact noFourCycle_unique h_c4 hu0v hu0m' (h_zSet_adj_v m' hm'Z)
              (hAm u0 hu0A) (h_zSet_adj_v m hmZ)
          have hms : s m ≠ s v := h_zSet_color m hmZ
          have hbW_ge : n ≤ bW := by
            by_contra hlt
            have h1 := hv_B
            have h2 := hmB
            dsimp [B] at h1 h2
            rw [varSet_input n C g bW (by omega)] at h1 h2
            simp only [Finset.mem_singleton] at h1 h2
            subst h1; subst h2
            exact hms rfl
          let jb := bW - n
          have hbW_eq : bW = n + jb := by omega
          have hjb_lt : jb < g := by omega
          have haW_ne : aW ≠ n + jb := by
            intro heq
            have : m ∈ A := by
              dsimp [A]; rw [heq, ← hbW_eq]; exact hmB
            exact hms (hA_L m this)
          have hno_jb : ∀ k < C.gates.length, k ≠ g → n + jb ∉ (gateAt C k).inputs := by
            intro k hk hkg hmem
            have hjk : jb < k := by
              have := hAO.2.1 k hk (n + jb) hmem; omega
            by_cases hbf : BelowF G C k
            · rcases hAO.1 _ (gateAt_mem hk) with hop | hop
              · rw [gate_inputs_eq hAO hk] at hmem
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
                rcases hmem with heq | heq
                · exact h_clean_and_no_two_sided k hk hop hkg 0
                    ⟨⟨v, by rw [← heq, ← hbW_eq]; exact hv_B, rfl⟩,
                     ⟨m, by rw [← heq, ← hbW_eq]; exact hmB, hms⟩⟩
                · exact h_clean_and_no_two_sided k hk hop hkg 1
                    ⟨⟨v, by rw [← heq, ← hbW_eq]; exact hv_B, rfl⟩,
                     ⟨m, by rw [← heq, ← hbW_eq]; exact hmB, hms⟩⟩
              · rw [gate_inputs_eq hAO hk] at hmem
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
                rcases hmem with heq | heq
                · have hi := h_clean_or_inputs k hk hbf hop 0
                  rw [← heq] at hi
                  apply hbW_d
                  rw [hbW_eq]
                  have : n + jb - n = jb := by omega
                  rw [this] at hi
                  exact hi.2.2
                · have hi := h_clean_or_inputs k hk hbf hop 1
                  rw [← heq] at hi
                  apply hbW_d
                  rw [hbW_eq]
                  have : n + jb - n = jb := by omega
                  rw [this] at hi
                  exact hi.2.2
            · have hsub : B ⊆ varSet n C g (n + k) := by
                rw [varSet_gate hAO g k hk hkg]
                rw [gate_inputs_eq hAO hk] at hmem
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
                rcases hmem with heq | heq
                · rw [← heq, ← hbW_eq]; exact Finset.subset_union_left
                · rw [← heq, ← hbW_eq]; exact Finset.subset_union_right
              have hle := h_two_sided_le_b k hk hbf hkg ⟨v, hsub hv_B, rfl⟩ ⟨m, hsub hmB, hms⟩
              omega
          exfalso
          apply h_exception aW bW v m
          refine ⟨haW_lt,hbW_lt,hbW_ge,?_,haWmem,hbWmem,haW_val,hbW_val,hg_ab,
            hAB_inter,hv_A,hv_B,hmB,⟨u0,hu0A,hu0v⟩,hAm,hA_L,?_,?_,hBZ_uniq,h_wval_dirty⟩
          · simpa only [hbW_eq] using haW_ne
          · intro k hk hkg
            simpa only [hbW_eq] using hno_jb k hk hkg
          · exact (h_mem_zSet m).mp hmZ
      · push_neg at hBZ
        let D := delCircuit n C g v.val
        have hvl : v.val < n + g := by omega
        have hAO' := delCircuit_isAO2 hAO hg_lt hvl
        have hle_v : ∀ x, wval C x v.val = true → gateVal n C g x = true := by
          intro x hxv
          rw [wval_input C x v.val v.isLt] at hxv
          rw [hg_AB]
          exact ⟨⟨v, hv_A, hxv⟩, ⟨v, hv_B, hxv⟩⟩
        have h_edge_keep : ∀ p q : Fin n, G.Adj p q → s p = s v →
            ∀ k < C.gates.length, BelowF G C k →
              gateVal n C k (pairInput p q) = true →
              gateVal n D (delGateMap g k) (pairInput p q) = true := by
          intro p q hpq hsp k
          have hsq : s q ≠ s v := fun heq => h_bip p q hpq (hsp.trans heq.symm)
          induction k using Nat.strongRecOn with
          | ind k ih =>
            intro hk hbf hCk
            have hkg : k ≠ g := fun heq => hg_dirty (heq ▸ hbf)
            have hk' : delGateMap g k < D.gates.length := by
              rw [delCircuit_len]; unfold delGateMap; split_ifs <;> omega
            rcases hAO.1 _ (gateAt_mem hk) with hop | hop
            · have hgate : (gateAt D (delGateMap g k)).op = GateOp.and := by
                rw [delCircuit_gateAt_src hg_lt hk hkg, hop]
              change wval C (pairInput p q) (n + k) = true at hCk
              rw [wval_gate_and hAO _ hk hop, Bool.and_eq_true] at hCk
              change wval D (pairInput p q) (n + delGateMap g k) = true
              rw [wval_gate_and hAO' _ hk' hgate, Bool.and_eq_true,
                delCircuit_opnd hAO hg_lt hk hkg 0, delCircuit_opnd hAO hg_lt hk hkg 1]
              have hd0 : ¬ WireBelowF G C (opnd C k 0) := h_no_imp k hk hop _ (opnd_mem hAO hk 0)
              have hd1 : ¬ WireBelowF G C (opnd C k 1) := h_no_imp k hk hop _ (opnd_mem hAO hk 1)
              have h0 := (h_wval_dirty _ (by have := opnd_lt hAO hk 0; omega) hd0 _).mp hCk.1
              have h1 := (h_wval_dirty _ (by have := opnd_lt hAO hk 1; omega) hd1 _).mp hCk.2
              have h_g_to_v : (∃ z ∈ Z, pairInput p q z = true) →
                  gateVal n C g (pairInput p q) = true → wval C (pairInput p q) v.val = true := by
                rintro ⟨z, hzZ, hpqz⟩ hgx
                simp only [pairInput, decide_eq_true_eq] at hpqz
                have hzq : z = q := by
                  rcases hpqz with rfl | rfl
                  · exact (h_zSet_color z hzZ hsp).elim
                  · rfl
                have hqZ : q ∈ Z := hzq ▸ hzZ
                rcases (hg_AB (pairInput p q)).mp hgx with ⟨⟨u, huA, hpqu⟩, ⟨w, hwB, hpqw⟩⟩
                simp only [pairInput, decide_eq_true_eq] at hpqu hpqw
                have hpA : p ∈ A := by
                  rcases hpqu with rfl | huq
                  · exact huA
                  · exact (hsq (huq ▸ hA_L u huA)).elim
                have hpB : p ∈ B := by
                  rcases hpqw with rfl | hwq
                  · exact hwB
                  · exact (hBZ q (hwq ▸ hwB) hqZ).elim
                have hpv : p = v := hAB_inter p hpA hpB
                subst hpv
                rw [wval_input C _ p.val p.isLt]
                simp [pairInput]
              rw [h_del_wval_dirty v.val hvl _ (by have := opnd_lt hAO hk 0; omega) hd0,
                h_del_wval_dirty v.val hvl _ (by have := opnd_lt hAO hk 1; omega) hd1]
              rcases h0 with ⟨hu0, hgx⟩ | h0s
              · have hu1f : usesG n C g (opnd C k 1) = false := by
                  cases h : usesG n C g (opnd C k 1)
                  · rfl
                  · exact (h_and_not_both_g k hk hop hkg ⟨hu0, h⟩).elim
                rcases h1 with ⟨hu1t, _⟩ | ⟨z, hz, hpqz⟩
                · rw [hu1f] at hu1t; cases hu1t
                · have hzZ : z ∈ Z := (h_mem_zSet z).mpr ⟨k, hk, hop, hkg, Or.inl ⟨hu0, hz⟩⟩
                  exact ⟨Or.inl ⟨hu0, h_g_to_v ⟨z, hzZ, hpqz⟩ hgx⟩, Or.inr ⟨z, hz, hpqz⟩⟩
              · rcases h1 with ⟨hu1, hgx⟩ | h1s
                · rcases h0s with ⟨z, hz, hpqz⟩
                  have hzZ : z ∈ Z := (h_mem_zSet z).mpr ⟨k, hk, hop, hkg, Or.inr ⟨hu1, hz⟩⟩
                  exact ⟨Or.inr ⟨z, hz, hpqz⟩, Or.inl ⟨hu1, h_g_to_v ⟨z, hzZ, hpqz⟩ hgx⟩⟩
                · exact ⟨Or.inr h0s, Or.inr h1s⟩
            · have hgate : (gateAt D (delGateMap g k)).op = GateOp.or := by
                rw [delCircuit_gateAt_src hg_lt hk hkg, hop]
              change wval C (pairInput p q) (n + k) = true at hCk
              rw [wval_gate_or hAO _ hk hop, Bool.or_eq_true] at hCk
              change wval D (pairInput p q) (n + delGateMap g k) = true
              rw [wval_gate_or hAO' _ hk' hgate, Bool.or_eq_true,
                delCircuit_opnd hAO hg_lt hk hkg 0, delCircuit_opnd hAO hg_lt hk hkg 1]
              have hi0 := h_clean_or_inputs k hk hbf hop 0
              have hi1 := h_clean_or_inputs k hk hbf hop 1
              have hne0 : opnd C k 0 - n ≠ g := fun heq => hg_dirty (heq ▸ hi0.2.2)
              have hne1 : opnd C k 1 - n ≠ g := fun heq => hg_dirty (heq ▸ hi1.2.2)
              have heq0 : opnd C k 0 = n + (opnd C k 0 - n) := by omega
              have heq1 : opnd C k 1 = n + (opnd C k 1 - n) := by omega
              rcases hCk with h0 | h1
              · left
                rw [heq0, delMap_gate n g v.val _ hne0]
                exact ih _ hi0.2.1 (by omega) hi0.2.2
                  (by change wval C (pairInput p q) (n + (opnd C k 0 - n)) = true; rw [← heq0]; exact h0)
              · right
                rw [heq1, delMap_gate n g v.val _ hne1]
                exact ih _ hi1.2.1 (by omega) hi1.2.2
                  (by change wval C (pairInput p q) (n + (opnd C k 1 - n)) = true; rw [← heq1]; exact h1)
        refine ⟨D, hAO', delCircuit_size_strict n C g v.val hg_lt, ?_, ?_⟩
        · apply circuitFun_eq_graphFun_of hAO'
          · intro x hx
            exact h_out_below x (delCircuit_wval_le hAO hg_lt hvl x (hle_v x) C.output (by omega) hx)
          · intro p q hpq
            have hCpq : gateVal n C (C.output - n) (pairInput p q) = true := by
              have h1 : circuitFun n C (pairInput p q) = true := by
                rw [h_eq]; exact (graphFun_pairInput_iff G p q).mpr hpq
              change wval C (pairInput p q) C.output = true at h1
              have : C.output = n + (C.output - n) := by omega
              rw [this] at h1; exact h1
            have hDout : ∀ y, circuitFun n D y = gateVal n D (delGateMap g (C.output - n)) y := by
              intro y
              change wval D y (delMap n g v.val C.output) = wval D y (n + delGateMap g (C.output - n))
              have h_out_ne : C.output - n ≠ g := by omega
              have h_out_eq : C.output = n + (C.output - n) := by omega
              conv_lhs => rw [h_out_eq]
              rw [delMap_gate n g v.val _ h_out_ne]
            by_cases hsp : s p = s v
            · rw [hDout]
              exact h_edge_keep p q hpq hsp (C.output - n) (by omega) h_out_below_gate hCpq
            · have hsq : s q = s v := bool_eq_of_ne_ne (h_bip p q hpq) hsp
              have hsym : pairInput p q = pairInput q p := by
                funext t; simp [pairInput, or_comm]
              rw [hsym, hDout]
              exact h_edge_keep q p hpq.symm hsq (C.output - n) (by omega) h_out_below_gate (hsym ▸ hCpq)
        · intro k' hk' hop' x hDx
          rw [delCircuit_len] at hk'
          let src := if k' < g then k' else k' + 1
          have hsrc_lt : src < C.gates.length := by dsimp [src]; split_ifs <;> omega
          have hsrc_ne : src ≠ g := by dsimp [src]; split_ifs <;> omega
          have hdgm : delGateMap g src = k' := by dsimp [src, delGateMap]; split_ifs <;> omega
          have hop : (gateAt C src).op = GateOp.and := by
            rw [← hdgm, delCircuit_gateAt_src hg_lt hsrc_lt hsrc_ne] at hop'
            exact hop'
          apply h_clean_and src hsrc_lt hop hsrc_ne x
          apply delCircuit_wval_le hAO hg_lt hvl x (hle_v x) (n + src) (by omega)
          rw [delMap_gate n g v.val src hsrc_ne, hdgm]
          exact hDx
  by_cases h0L : ∀ u ∈ varSet n C g (opnd C g 0), s u = s v
  · exact h_solve_ordered (opnd C g 0) (opnd C g 1) h_g_op0_lt h_g_op1_lt h_g_op0_dirty h_g_op1_dirty
      (fun x => wval_gate_and hAO x hg_lt hg_and)
      (fun w hw => by
        rw [gate_inputs_eq hAO hg_lt] at hw
        simpa using hw)
      (opnd_mem hAO hg_lt 0) (opnd_mem hAO hg_lt 1) h0L
  · have h1L : ∀ w ∈ varSet n C g (opnd C g 1), s w = s v := by
      push_neg at h0L
      rcases h0L with ⟨u, hu, hsu⟩
      intro w hw
      by_contra hsw
      rcases h_zSet_nonempty with ⟨z, hzZ⟩
      have hsz := h_zSet_color z hzZ
      have htri : graphFun G ∅ (tripleInput u w z) = true := by
        apply h_zSet_below z hzZ (tripleInput u w z)
        · rw [h_g_val]
          exact ⟨⟨u, hu, by simp [tripleInput]⟩, ⟨w, hw, by simp [tripleInput]⟩⟩
        · simp [tripleInput]
      rw [graphFun_tripleInput_iff] at htri
      rcases htri with hadj | hadj | hadj
      · exact h_bip u w hadj (bool_eq_of_ne_ne (Ne.symm hsu) (Ne.symm hsw))
      · exact h_bip u z hadj (bool_eq_of_ne_ne (Ne.symm hsu) (Ne.symm hsz))
      · exact h_bip w z hadj (bool_eq_of_ne_ne (Ne.symm hsw) (Ne.symm hsz))
    exact h_solve_ordered (opnd C g 1) (opnd C g 0) h_g_op1_lt h_g_op0_lt h_g_op1_dirty h_g_op0_dirty
      (fun x => (wval_gate_and hAO x hg_lt hg_and).trans (Bool.and_comm _ _))
      (fun w hw => by
        rw [gate_inputs_eq hAO hg_lt] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        exact hw.symm)
      (opnd_mem hAO hg_lt 1) (opnd_mem hAO hg_lt 0) h1L


lemma least_exceptional (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (g : ℕ)
    (h_bip : ∀u v : Fin n,G.Adj u v → s u≠s v) (h_c4 : NoFourCycle G)
    (h_least : IsLeastAO G C) (h_lift : IsLiftFixedPoint G C)
    (h_no_imp : ∀k<C.gates.length,(gateAt C k).op=GateOp.and →
      ∀t∈(gateAt C k).inputs,¬∀x : Fin n → Bool,
        Circuit.eval ⟨C.gates,t⟩ (List.ofFn x)=true → graphFun G ∅ x=true)
    (h_cone : ∀k<C.gates.length,InOutputCone n C k)
    (hg : g<C.gates.length) (hand : (gateAt C g).op=GateOp.and)
    (hdirty : ¬BelowF G C g)
    (hunique : ∀k<C.gates.length,(gateAt C k).op=GateOp.and → k≠g → BelowF G C k)
    (hunit : ∃v : Fin n,gateVal n C g (unitInput v)=true) :
    ∃(aW bW : ℕ)(v m : Fin n),Exceptional G C s g aW bW v m := by
  classical
  by_contra hn
  have hexc : ∀(aW bW : ℕ)(v m : Fin n),Exceptional G C s g aW bW v m → False := by
    intro aW bW v m h
    exact hn ⟨aW,bW,v,m,h⟩
  obtain ⟨D,hD,hsmall,hfun,_⟩ := main n G C s g h_bip h_c4 h_least.1 h_least.2.1
    h_lift h_no_imp h_cone hg hand hdirty hunique hunit hexc
  exact (Nat.not_lt_of_ge (h_least.2.2 D hD hfun)) hsmall


lemma usesG_reach {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (g : ℕ) :
    ∀w,w<n+C.gates.length → usesG n C g w=true →
      ∃k,w=n+k ∧ k<C.gates.length ∧ (g=k ∨ InCone n C g k) := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw ht
    by_cases hraw : w<n
    · rw [usesG_input n C g w hraw] at ht
      cases ht
    by_cases hself : w=n+g
    · exact ⟨g,hself,by omega,Or.inl rfl⟩
    let k := w-n
    have hwk : w=n+k := by dsimp [k];omega
    have hk : k<C.gates.length := by omega
    have hkg : k≠g := by omega
    rw [hwk,usesG_gate hAO g k hk hkg,Bool.or_eq_true] at ht
    have hchild : ∀b : Fin 2,usesG n C g (opnd C k b)=true → InCone n C g k := by
      intro b hb
      have hlt : opnd C k b<w := by have := opnd_lt hAO hk b;omega
      obtain ⟨l,hl,hll,hreach⟩ := ih (opnd C k b) hlt (by omega) hb
      apply (inCone_iff hk).mpr
      refine ⟨opnd C k b,opnd_mem hAO hk b,by omega,opnd_lt hAO hk b,?_⟩
      have he : opnd C k b-n=l := by omega
      rw [he]
      exact hreach
    refine ⟨k,hwk,hk,Or.inr ?_⟩
    rcases ht with h0 | h1
    · exact hchild 0 h0
    · exact hchild 1 h1

end PEqualNP.Outside.L_meta_3754.Strict3653
