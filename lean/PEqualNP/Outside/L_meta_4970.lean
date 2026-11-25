import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_4970_aux.H5Pruning

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj



open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def wireFn (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wireFn_mono (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (w : ℕ) :
    Monotone (wireFn n C w) := by
  intro x y hxy
  have hm : wireFn n C w x = true → wireFn n C w y = true := by
    apply wiresFrom_mono C.gates hC.1 (List.ofFn x) (List.ofFn y) (by simp)
    intro i hi
    by_cases hin : i < n
    · have hi' : x ⟨i, hin⟩ = true := by
        rw [List.getD_eq_getElem _ _ (by simpa using hin)] at hi
        simpa only [List.getElem_ofFn] using hi
      have hle := hxy ⟨i, hin⟩
      rw [List.getD_eq_getElem _ _ (by simpa using hin)]
      simpa only [List.getElem_ofFn] using (Bool.le_iff_imp.mp hle hi')
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hin)] at hi
      cases hi
  exact Bool.le_iff_imp.mpr hm

def zeroed (C : Circuit) (j : ℕ) : Circuit :=
  ⟨C.gates.take j ++ ⟨GateOp.or, []⟩ :: C.gates.drop (j + 1), C.output⟩

lemma zeroed_wires (C : Circuit) (j : ℕ) (x : List Bool) :
    (zeroed C j).wires x =
      wiresFrom (C.gates.drop (j + 1)) (wiresFrom (C.gates.take j) x ++ [false]) := by
  change wiresFrom (C.gates.take j ++ ⟨GateOp.or, []⟩ :: C.gates.drop (j + 1)) x = _
  rw [wiresFrom_append]
  rfl

lemma wires_split (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (x : List Bool) :
    C.wires x =
      wiresFrom (C.gates.drop (j + 1))
        (wiresFrom (C.gates.take j) x ++
          [(C.gates[j]).op.eval
            ((C.gates[j]).inputs.map fun i => (wiresFrom (C.gates.take j) x).getD i false)]) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have h := (List.take_append_drop j C.gates).symm
    rw [List.drop_eq_getElem_cons hj] at h
    exact h
  change wiresFrom C.gates x = _
  conv_lhs => rw [hsplit, wiresFrom_append]
  rfl

lemma zeroed_eq_of_wire_false (n : ℕ) (C : Circuit) (j : ℕ)
    (hj : j < C.gates.length) (x : Fin n → Bool)
    (hz : wireFn n C (n + j) x = false) :
    (zeroed C j).wires (List.ofFn x) = C.wires (List.ofFn x) := by
  let pre := wiresFrom (C.gates.take j) (List.ofFn x)
  let v := (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => pre.getD i false)
  have hlen : pre.length = n + j := by
    simp [pre, length_wiresFrom, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hsplit : C.wires (List.ofFn x) =
      wiresFrom (C.gates.drop (j + 1)) (pre ++ [v]) := wires_split C j hj _
  have hv : v = false := by
    unfold wireFn at hz
    rw [hsplit, getD_wiresFrom_lt] at hz
    · simpa [← hlen] using hz
    · simp [hlen]
  rw [zeroed_wires, hsplit, hv]

lemma zeroed_andOr (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (j : ℕ) :
    ∀ g ∈ (zeroed C j).gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  simp only [zeroed, List.mem_append, List.mem_cons] at hg
  rcases hg with hg | rfl | hg
  · exact hC.1 g (List.mem_of_mem_take hg)
  · exact Or.inr rfl
  · exact hC.1 g (List.mem_of_mem_drop hg)

lemma wireFn_mono_of_andOr (n : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) (w : ℕ) :
    Monotone (wireFn n C w) := by
  intro x y hxy
  apply Bool.le_iff_imp.mpr
  apply wiresFrom_mono C.gates hC (List.ofFn x) (List.ofFn y) (by simp)
  intro i hi
  by_cases hin : i < n
  · have hi' : x ⟨i, hin⟩ = true := by
      rw [List.getD_eq_getElem _ _ (by simpa using hin)] at hi
      simpa only [List.getElem_ofFn] using hi
    rw [List.getD_eq_getElem _ _ (by simpa using hin)]
    simpa only [List.getElem_ofFn] using (Bool.le_iff_imp.mp (hxy ⟨i, hin⟩) hi')
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hin)] at hi
    cases hi

lemma zeroed_wire_mono (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (j w : ℕ) :
    Monotone (wireFn n (zeroed C j) w) :=
  wireFn_mono_of_andOr n _ (zeroed_andOr n C hC j) w

lemma zeroed_wire_le (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (w : ℕ) (x : Fin n → Bool) :
    wireFn n (zeroed C j) w x ≤ wireFn n C w x := by
  apply Bool.le_iff_imp.mpr
  unfold wireFn
  rw [zeroed_wires, wires_split C j hj]
  apply wiresFrom_mono (C.gates.drop (j + 1))
    (fun g hg => hC.1 g (List.mem_of_mem_drop hg)) _ _ (by simp)
  intro i hi
  let pre := wiresFrom (C.gates.take j) (List.ofFn x)
  change (pre ++ [false]).getD i false = true at hi
  by_cases hlt : i < pre.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    rw [List.getD_append _ _ _ _ hlt]
    exact hi
  · have hzero : (pre ++ [false]).getD i false = false := by
      by_cases heq : i = pre.length
      · subst i
        simp
      · exact List.getD_eq_default _ _ (by simp; omega)
    rw [hzero] at hi
    cases hi

def pairInput {n : ℕ} (u v : Fin n) : Fin n → Bool :=
  fun i => decide (i = u ∨ i = v)

def singletonInput {n : ℕ} (u : Fin n) : Fin n → Bool :=
  fun i => decide (i = u)

def graphFun {n : ℕ} (E : Finset (Fin n × Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ e ∈ E, x e.1 = true ∧ x e.2 = true)

def starFun {n : ℕ} (Q : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ q ∈ Q, x q = true)

lemma pairInput_le {n : ℕ} (u v : Fin n) (x : Fin n → Bool)
    (hu : x u = true) (hv : x v = true) : pairInput u v ≤ x := by
  intro i
  by_cases hi : i = u ∨ i = v
  · rcases hi with rfl | rfl <;> simp [pairInput, hu, hv]
  · simp [pairInput, hi]

lemma singletonInput_le {n : ℕ} (u : Fin n) (x : Fin n → Bool)
    (hu : x u = true) : singletonInput u ≤ x := by
  intro i
  by_cases hi : i = u
  · subst i
    simp [singletonInput, hu]
  · simp [singletonInput, hi]

lemma zeroed_graph_preserved (n : ℕ) (E : Finset (Fin n × Fin n))
    (C : Circuit) (hC : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (hzero : ∀ e ∈ E, wireFn n C (n + j) (pairInput e.1 e.2) = false)
    (w : ℕ) (hspec : ∀ x, wireFn n C w x = graphFun E x) :
    ∀ x, wireFn n (zeroed C j) w x = graphFun E x := by
  intro x
  cases hx : graphFun E x with
  | false =>
    have hle := zeroed_wire_le n C hC j hj w x
    rw [hspec, hx] at hle
    exact le_antisymm hle (by cases wireFn n (zeroed C j) w x <;> decide)
  | true =>
    obtain ⟨e, he, hu, hv⟩ := (of_decide_eq_true hx : ∃ e ∈ E, x e.1 = true ∧ x e.2 = true)
    have hp : wireFn n C w (pairInput e.1 e.2) = true := by
      rw [hspec]
      apply decide_eq_true
      exact ⟨e, he, by simp [pairInput], by simp [pairInput]⟩
    have hsame := zeroed_eq_of_wire_false n C j hj (pairInput e.1 e.2) (hzero e he)
    have hpz : wireFn n (zeroed C j) w (pairInput e.1 e.2) = true := by
      unfold wireFn
      rw [hsame]
      exact hp
    have hle := zeroed_wire_mono n C hC j w (pairInput_le e.1 e.2 x hu hv)
    exact Bool.le_iff_imp.mp hle hpz

lemma zeroed_star_preserved_of_singletons (n : ℕ) (Q : Finset (Fin n))
    (C : Circuit) (hC : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (hzero : ∀ q ∈ Q, wireFn n C (n + j) (singletonInput q) = false)
    (w : ℕ) (hspec : ∀ x, wireFn n C w x = starFun Q x) :
    ∀ x, wireFn n (zeroed C j) w x = starFun Q x := by
  intro x
  cases hx : starFun Q x with
  | false =>
    have hle := zeroed_wire_le n C hC j hj w x
    rw [hspec, hx] at hle
    exact le_antisymm hle (by cases wireFn n (zeroed C j) w x <;> decide)
  | true =>
    obtain ⟨q, hq, hqx⟩ := (of_decide_eq_true hx : ∃ q ∈ Q, x q = true)
    have hp : wireFn n C w (singletonInput q) = true := by
      rw [hspec]
      apply decide_eq_true
      exact ⟨q, hq, by simp [singletonInput]⟩
    have hsame := zeroed_eq_of_wire_false n C j hj (singletonInput q) (hzero q hq)
    have hpz : wireFn n (zeroed C j) w (singletonInput q) = true := by
      unfold wireFn
      rw [hsame]
      exact hp
    have hle := zeroed_wire_mono n C hC j w (singletonInput_le q x hqx)
    exact Bool.le_iff_imp.mp hle hpz

lemma zeroed_star_preserved (n : ℕ) (E : Finset (Fin n × Fin n))
    (Q : Finset (Fin n)) (hactive : ∀ q ∈ Q, ∃ e ∈ E, q = e.1 ∨ q = e.2)
    (C : Circuit) (hC : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (hzero : ∀ e ∈ E, wireFn n C (n + j) (pairInput e.1 e.2) = false)
    (w : ℕ) (hspec : ∀ x, wireFn n C w x = starFun Q x) :
    ∀ x, wireFn n (zeroed C j) w x = starFun Q x := by
  apply zeroed_star_preserved_of_singletons n Q C hC j hj _ w hspec
  intro q hq
  obtain ⟨e, he, hqe⟩ := hactive q hq
  have hqpair : pairInput e.1 e.2 q = true := by
    simp only [pairInput, decide_eq_true_eq]
    exact hqe
  have hle := wireFn_mono n C hC (n + j)
    (singletonInput_le q (pairInput e.1 e.2) hqpair)
  rw [hzero e he] at hle
  exact le_antisymm hle (by cases wireFn n C (n + j) (singletonInput q) <;> decide)

def bipartiteEdges {p l : ℕ} (E : Finset (Fin p × Fin l)) :
    Finset (Fin (p + l) × Fin (p + l)) :=
  E.image fun e => (Fin.castAdd l e.1, Fin.natAdd p e.2)

lemma graphFun_bipartite {p l : ℕ} (E : Finset (Fin p × Fin l))
    (x : Fin (p + l) → Bool) :
    graphFun (bipartiteEdges E) x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true) := by
  simp only [graphFun, bipartiteEdges, Finset.mem_image]
  congr 1
  apply propext
  constructor
  · rintro ⟨e, ⟨ab, hab, rfl⟩, ha, hb⟩
    exact ⟨ab.1, ab.2, hab, ha, hb⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    exact ⟨_, ⟨(a, b), hab, rfl⟩, ha, hb⟩

lemma zeroed_bipartite_output_preserved {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : IsAO2 (p + l) C) (j : ℕ) (hj : j < C.gates.length)
    (hzero : ∀ a b, (a, b) ∈ E →
      wireFn (p + l) C (p + l + j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = false)
    (hspec : ∀ x : Fin (p + l) → Bool,
      PEqualNP.MetaComplexity.circuitFun (p + l) C x =
        decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
          x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    ∀ x : Fin (p + l) → Bool,
      PEqualNP.MetaComplexity.circuitFun (p + l) (zeroed C j) x =
        decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
          x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true) := by
  have hz : ∀ e ∈ bipartiteEdges E,
      wireFn (p + l) C (p + l + j) (pairInput e.1 e.2) = false := by
    intro e he
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp he
    exact hzero ab.1 ab.2 hab
  have hs : ∀ x, wireFn (p + l) C C.output x = graphFun (bipartiteEdges E) x := by
    intro x
    rw [graphFun_bipartite]
    exact hspec x
  intro x
  have h := zeroed_graph_preserved (p + l) (bipartiteEdges E) C hC j hj hz C.output hs x
  rw [graphFun_bipartite] at h
  exact h

lemma zeroed_left_star_preserved {p l : ℕ} (E : Finset (Fin p × Fin l))
    (a : Fin p) (Q : Finset (Fin l)) (hQ : ∀ b ∈ Q, (a, b) ∈ E)
    (C : Circuit) (hC : IsAO2 (p + l) C) (j : ℕ) (hj : j < C.gates.length)
    (hzero : ∀ a b, (a, b) ∈ E →
      wireFn (p + l) C (p + l + j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = false)
    (w : ℕ) (hspec : ∀ x : Fin (p + l) → Bool,
      wireFn (p + l) C w x = decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)) :
    ∀ x : Fin (p + l) → Bool,
      wireFn (p + l) (zeroed C j) w x = decide (∃ b ∈ Q, x (Fin.natAdd p b) = true) := by
  let Q' := Q.image (Fin.natAdd p)
  have hs : ∀ x, wireFn (p + l) C w x = starFun Q' x := by
    intro x
    simpa [starFun, Q'] using hspec x
  have ha : ∀ q ∈ Q', ∃ e ∈ bipartiteEdges E, q = e.1 ∨ q = e.2 := by
    intro q hq
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
    refine ⟨(Fin.castAdd l a, Fin.natAdd p b), ?_, Or.inr rfl⟩
    exact Finset.mem_image.mpr ⟨(a, b), hQ b hb, rfl⟩
  have hz : ∀ e ∈ bipartiteEdges E,
      wireFn (p + l) C (p + l + j) (pairInput e.1 e.2) = false := by
    intro e he
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp he
    exact hzero ab.1 ab.2 hab
  intro x
  have h := zeroed_star_preserved (p + l) (bipartiteEdges E) Q' ha C hC j hj hz w hs x
  simpa [starFun, Q'] using h

lemma zeroed_right_star_preserved {p l : ℕ} (E : Finset (Fin p × Fin l))
    (b : Fin l) (P : Finset (Fin p)) (hP : ∀ a ∈ P, (a, b) ∈ E)
    (C : Circuit) (hC : IsAO2 (p + l) C) (j : ℕ) (hj : j < C.gates.length)
    (hzero : ∀ a b, (a, b) ∈ E →
      wireFn (p + l) C (p + l + j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = false)
    (w : ℕ) (hspec : ∀ x : Fin (p + l) → Bool,
      wireFn (p + l) C w x = decide (∃ a ∈ P, x (Fin.castAdd l a) = true)) :
    ∀ x : Fin (p + l) → Bool,
      wireFn (p + l) (zeroed C j) w x = decide (∃ a ∈ P, x (Fin.castAdd l a) = true) := by
  let P' := P.image (Fin.castAdd l)
  have hs : ∀ x, wireFn (p + l) C w x = starFun P' x := by
    intro x
    simpa [starFun, P'] using hspec x
  have ha : ∀ q ∈ P', ∃ e ∈ bipartiteEdges E, q = e.1 ∨ q = e.2 := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    refine ⟨(Fin.castAdd l a, Fin.natAdd p b), ?_, Or.inl rfl⟩
    exact Finset.mem_image.mpr ⟨(a, b), hP a ha, rfl⟩
  have hz : ∀ e ∈ bipartiteEdges E,
      wireFn (p + l) C (p + l + j) (pairInput e.1 e.2) = false := by
    intro e he
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp he
    exact hzero ab.1 ab.2 hab
  intro x
  have h := zeroed_star_preserved (p + l) (bipartiteEdges E) P' ha C hC j hj hz w hs x
  simpa [starFun, P'] using h

lemma wireFn_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) (x : Fin n → Bool) :
    wireFn n C w x = x ⟨w, hw⟩ := by
  unfold wireFn Circuit.wires
  change (wiresFrom C.gates (List.ofFn x)).getD w false = _
  rw [getD_wiresFrom_lt _ _ _ (by simpa using hw)]
  rw [List.getD_eq_getElem _ _ (by simpa using hw)]
  simp

lemma gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, hj]

lemma binary_gate (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, a < n + j ∧ b < n + j ∧
      (gateAt C j).inputs = [a, b] ∧
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ x, wireFn n C (n + j) x =
        (gateAt C j).op.eval [wireFn n C a x, wireFn n C b x] := by
  have hmem : gateAt C j ∈ C.gates := by
    rw [gateAt_get C j hj]
    exact List.getElem_mem hj
  have hlen := hC.2.2 _ hmem
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  have ha : a < n + j := hC.2.1 j hj a (by simp [hab])
  have hb : b < n + j := hC.2.1 j hj b (by simp [hab])
  refine ⟨a, b, ha, hb, hab, hC.1 _ hmem, ?_⟩
  intro x
  unfold wireFn
  change (wiresFrom C.gates (List.ofFn x)).getD (n + j) false = _
  have he := getD_wiresFrom_gate C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at he
  rw [he, ← gateAt_get C j hj, hab]
  simp [ha, hb, wiresFrom, Circuit.wires]

lemma wireFn_ge (n : ℕ) (C : Circuit) (w : ℕ) (hw : n + C.gates.length ≤ w)
    (x : Fin n → Bool) : wireFn n C w x = false := by
  unfold wireFn Circuit.wires
  change (wiresFrom C.gates (List.ofFn x)).getD w false = false
  apply List.getD_eq_default
  simpa only [length_wiresFrom, List.length_ofFn] using hw


lemma monotone_factor_eq_star {n : ℕ}
    (Q : Finset (Fin n)) (f : (Fin n → Bool) → Bool) (hf : Monotone f)
    (hz : f (fun i => decide (i ∉ Q)) = false)
    (hcontains : ∀ x, starFun Q x = true → f x = true) :
    ∀ x, f x = starFun Q x := by
  intro x
  cases hx : starFun Q x with
  | false =>
      have hzero : ∀ i ∈ Q, x i = false := by
        intro i hi
        cases hxi : x i with
        | false => rfl
        | true =>
            have : starFun Q x = true := by
              simp only [starFun, decide_eq_true_eq]
              exact ⟨i, hi, hxi⟩
            simp [hx] at this
      have hle : x ≤ fun i => decide (i ∉ Q) := by
        intro i
        by_cases hi : i ∈ Q
        · simp [hi, hzero i hi]
        · simp [hi]
      have hfx := hf hle
      rw [hz] at hfx
      exact le_antisymm hfx (by cases f x <;> decide)
  | true => exact hcontains x hx

lemma monotone_and_eq_star {n : ℕ}
    (Q : Finset (Fin n)) (f g : (Fin n → Bool) → Bool)
    (hf : Monotone f) (hg : Monotone g)
    (h : ∀ x, (f x && g x) = starFun Q x) :
    (∀ x, f x = starFun Q x) ∨ (∀ x, g x = starFun Q x) := by
  have hcontains : ∀ x, starFun Q x = true → f x = true ∧ g x = true := by
    intro x hx
    have hh := h x
    rw [hx] at hh
    simpa only [Bool.and_eq_true] using hh
  have hz : starFun Q (fun i => decide (i ∉ Q)) = false := by
    simp [starFun]
  have hzfg : f (fun i => decide (i ∉ Q)) = false ∨
      g (fun i => decide (i ∉ Q)) = false := by
    have hh := h (fun i => decide (i ∉ Q))
    rw [hz] at hh
    simpa only [Bool.and_eq_false_iff] using hh
  rcases hzfg with hzf | hzg
  · exact Or.inl (monotone_factor_eq_star Q f hf hzf fun x hx => (hcontains x hx).1)
  · exact Or.inr (monotone_factor_eq_star Q g hg hzg fun x hx => (hcontains x hx).2)

lemma pure_star_not_input (n : ℕ) (C : Circuit) (Q : Finset (Fin n))
    (hQ : 2 ≤ Q.card) (w : ℕ) (hw : w < n)
    (hspec : ∀ x, wireFn n C w x = starFun Q x) : False := by
  have hsub : Q ⊆ {⟨w, hw⟩} := by
    intro q hq
    have hs := hspec (singletonInput q)
    rw [wireFn_input n C w hw] at hs
    have hstar : starFun Q (singletonInput q) = true := by
      apply decide_eq_true
      exact ⟨q, hq, by simp [singletonInput]⟩
    rw [hstar] at hs
    have heq : (⟨w, hw⟩ : Fin n) = q := of_decide_eq_true hs
    exact Finset.mem_singleton.mpr heq.symm
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at hc
  omega

lemma pure_star_valid (n : ℕ) (C : Circuit) (Q : Finset (Fin n))
    (hQ : Q.Nonempty) (w : ℕ)
    (hspec : ∀ x, wireFn n C w x = starFun Q x) : w < n + C.gates.length := by
  by_contra hn
  obtain ⟨q, hq⟩ := hQ
  have hs := hspec (singletonInput q)
  rw [wireFn_ge n C w (Nat.le_of_not_lt hn)] at hs
  have hstar : starFun Q (singletonInput q) = true := by
    apply decide_eq_true
    exact ⟨q, hq, by simp [singletonInput]⟩
  rw [hstar] at hs
  cases hs

lemma pure_star_or_root (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (hQ : 2 ≤ Q.card) (w : ℕ)
    (hspec : ∀ x, wireFn n C w x = starFun Q x) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.or ∧
      ∀ x, wireFn n C (n + j) x = starFun Q x := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have hn : n ≤ w := by
      by_contra hn
      exact pure_star_not_input n C Q hQ w (by omega) hspec
    have hw := pure_star_valid n C Q (Finset.card_pos.mp (by omega)) w hspec
    let j := w - n
    have hj : j < C.gates.length := by omega
    have hwj : n + j = w := by omega
    obtain ⟨a, b, ha, hb, _, hop, hval⟩ := binary_gate n C hC j hj
    rcases hop with hop | hop
    · have hand : ∀ x, (wireFn n C a x && wireFn n C b x) = starFun Q x := by
        intro x
        have hv := hval x
        rw [hwj, hspec, hop] at hv
        simpa [GateOp.eval] using hv.symm
      rcases monotone_and_eq_star Q (wireFn n C a) (wireFn n C b)
        (wireFn_mono n C hC a) (wireFn_mono n C hC b) hand with hleft | hright
      · exact ih a (by omega) hleft
      · exact ih b (by omega) hright
    · exact ⟨j, hj, hop, fun x => by simpa [hwj] using hspec x⟩

end PEqualNP.Outside.L_meta_4970_aux.H5Pruning



namespace PEqualNP.Outside.L_meta_4970_aux.H5Compile

open PEqualNP.CircuitLowerBounds

def wireValues (n : ℕ) (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)

lemma wireValues_length (n : ℕ) (gs : List Gate) (x : Fin n → Bool) :
    (wireValues n gs x).length = n + gs.length := by
  suffices h : ∀ gs : List Gate, ∀ w : List Bool,
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
        w.length + gs.length by
    simpa [wireValues] using h gs (List.ofFn x)
  intro gs
  induction gs with
  | nil => simp
  | cons g gs ih => intro w; simpa [List.foldl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])

lemma wireValues_append (n : ℕ) (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    wireValues n (gs ++ [g]) x = wireValues n gs x ++
      [g.op.eval (g.inputs.map fun i => (wireValues n gs x).getD i false)] := by
  simp [wireValues, List.foldl_append]

def pointerValue (w : List Bool) (r : Option ℕ) : Bool :=
  match r with
  | none => false
  | some i => w.getD i false

def validPointers (n : ℕ) (gs : List Gate) (rs : List (Option ℕ)) : Prop :=
  ∀ r ∈ rs, ∀ i, r = some i → i < n + gs.length

def emit (n : ℕ) (gs : List Gate) (op : GateOp) (a b : Option ℕ) : List Gate × Option ℕ :=
  match a, b with
  | some a, some b => (gs ++ [⟨op, [a,b]⟩], some (n + gs.length))
  | none, b => match op with
    | .or => (gs, b)
    | _ => (gs, none)
  | a, none => match op with
    | .or => (gs, a)
    | _ => (gs, none)

def step (n : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) : List Gate × List (Option ℕ) :=
  match g.inputs with
  | [a,b] =>
      let t := emit n s.1 g.op (s.2.getD a none) (s.2.getD b none)
      (t.1, s.2 ++ [t.2])
  | _ => (s.1, s.2 ++ [none])

def allowed (g : Gate) : Prop :=
  ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨ (g.op = .or ∧ g.inputs = [])

def binaryCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => g.inputs.length == 2)

lemma emit_size (n : ℕ) (gs : List Gate) (op : GateOp) (a b : Option ℕ) :
    (emit n gs op a b).1.length ≤ gs.length + 1 := by
  cases a <;> cases b <;> cases op <;> simp [emit]

lemma step_size (n : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) :
    (step n s g).1.length ≤ s.1.length + if g.inputs.length == 2 then 1 else 0 := by
  rcases g with ⟨op, ins⟩
  cases ins with
  | nil => simp [step]
  | cons a ins =>
      cases ins with
      | nil => simp [step]
      | cons b ins =>
          cases ins with
          | nil => simpa [step] using emit_size n s.1 op (s.2.getD a none) (s.2.getD b none)
          | cons c ins => simp [step]

lemma fold_size (n : ℕ) (gs : List Gate) (s : List Gate × List (Option ℕ)) :
    (gs.foldl (step n) s).1.length ≤ s.1.length + binaryCount gs := by
  induction gs generalizing s with
  | nil => simp [binaryCount]
  | cons g gs ih =>
      have h := ih (step n s g)
      have hs := step_size n s g
      simp only [List.foldl_cons]
      unfold binaryCount at *
      rw [List.countP_cons]
      by_cases hg : g.inputs.length = 2
      · simp [hg] at hs ⊢
        omega
      · simp [hg] at hs ⊢
        omega

def bounded (n : ℕ) (gs : List Gate) (r : Option ℕ) : Prop :=
  ∀ i, r = some i → i < n + gs.length

lemma pointer_append (n : ℕ) (gs : List Gate) (g : Gate) (r : Option ℕ)
    (hr : bounded n gs r) (x : Fin n → Bool) :
    pointerValue (wireValues n (gs ++ [g]) x) r = pointerValue (wireValues n gs x) r := by
  cases r with
  | none => rfl
  | some i =>
      simp only [pointerValue, wireValues_append]
      apply List.getD_append
      rw [wireValues_length]
      exact hr i rfl

lemma emit_preserves (n : ℕ) (gs : List Gate) (op : GateOp) (a b r : Option ℕ)
    (hr : bounded n gs r) (x : Fin n → Bool) :
    pointerValue (wireValues n (emit n gs op a b).1 x) r = pointerValue (wireValues n gs x) r := by
  cases a <;> cases b <;> cases op <;> simp only [emit]
  all_goals exact pointer_append n gs _ r hr x

lemma emit_value (n : ℕ) (gs : List Gate) (op : GateOp) (a b : Option ℕ)
    (hop : op = .and ∨ op = .or) (x : Fin n → Bool) :
    pointerValue (wireValues n (emit n gs op a b).1 x) (emit n gs op a b).2 =
      op.eval [pointerValue (wireValues n gs x) a, pointerValue (wireValues n gs x) b] := by
  rcases hop with rfl | rfl
  all_goals cases a <;> cases b <;> simp only [emit, pointerValue, wireValues_append]
  all_goals simp [GateOp.eval]
  all_goals rw [← wireValues_length n gs x]
  all_goals simp

lemma emit_bound (n : ℕ) (gs : List Gate) (op : GateOp) (a b : Option ℕ)
    (ha : bounded n gs a) (hb : bounded n gs b) :
    bounded n (emit n gs op a b).1 (emit n gs op a b).2 := by
  cases a <;> cases b <;> cases op <;> simp_all [emit, bounded]

lemma emit_old_bound (n : ℕ) (gs : List Gate) (op : GateOp) (a b r : Option ℕ)
    (hr : bounded n gs r) : bounded n (emit n gs op a b).1 r := by
  intro i hi
  have hlt := hr i hi
  cases a <;> cases b <;> cases op <;> simp only [emit, List.length_append, List.length_cons, List.length_nil]
  all_goals omega

lemma get_pointer_bound (n : ℕ) (gs : List Gate) (rs : List (Option ℕ))
    (hr : validPointers n gs rs) (k : ℕ) : bounded n gs (rs.getD k none) := by
  intro i hi
  by_cases hk : k < rs.length
  · rw [List.getD_eq_getElem _ _ hk] at hi
    exact hr _ (List.getElem_mem hk) i hi
  · rw [List.getD_eq_default _ _ (by omega)] at hi
    contradiction

lemma validPointers_append_none (n : ℕ) (gs : List Gate) (rs : List (Option ℕ))
    (hr : validPointers n gs rs) : validPointers n gs (rs ++ [none]) := by
  intro r hmem i hi
  simp only [List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hmem | rfl
  · exact hr r hmem i hi
  · contradiction

lemma step_bounds (n : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate)
    (hr : validPointers n s.1 s.2) : validPointers n (step n s g).1 (step n s g).2 := by
  rcases g with ⟨op,ins⟩
  cases ins with
  | nil => simpa only [step] using validPointers_append_none n s.1 s.2 hr
  | cons a ins =>
      cases ins with
      | nil => simpa only [step] using validPointers_append_none n s.1 s.2 hr
      | cons b ins =>
          cases ins with
          | cons c ins => simpa only [step] using validPointers_append_none n s.1 s.2 hr
          | nil =>
              intro r hmem i hi
              simp only [step, List.mem_append, List.mem_singleton] at hmem
              rcases hmem with hmem | rfl
              · exact emit_old_bound n s.1 op _ _ r (hr r hmem) i hi
              · exact emit_bound n s.1 op _ _ (get_pointer_bound n s.1 s.2 hr a)
                  (get_pointer_bound n s.1 s.2 hr b) i hi

lemma step_values (n : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate)
    (hr : validPointers n s.1 s.2) (hg : allowed g) (x : Fin n → Bool) :
    (step n s g).2.map (pointerValue (wireValues n (step n s g).1 x)) =
      s.2.map (pointerValue (wireValues n s.1 x)) ++
        [g.op.eval (g.inputs.map fun k =>
          (s.2.map (pointerValue (wireValues n s.1 x))).getD k false)] := by
  rcases g with ⟨op,ins⟩
  rcases hg with ⟨hop,hlen⟩ | ⟨hop,rfl⟩
  · obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp hlen
    simp only [step, List.map_append, List.map_cons, List.map_nil]
    have hm : List.map (pointerValue (wireValues n (emit n s.1 op (s.2.getD a none)
        (s.2.getD b none)).1 x)) s.2 = List.map (pointerValue (wireValues n s.1 x)) s.2 := by
      apply List.map_congr_left
      intro r hmem
      exact emit_preserves n s.1 op _ _ r (hr r hmem) x
    rw [hm, emit_value n s.1 op _ _ hop x]
    have ha := List.getD_map s.2 none (n := a) (pointerValue (wireValues n s.1 x))
    have hb := List.getD_map s.2 none (n := b) (pointerValue (wireValues n s.1 x))
    change (s.2.map (pointerValue (wireValues n s.1 x))).getD a false = _ at ha
    change (s.2.map (pointerValue (wireValues n s.1 x))).getD b false = _ at hb
    change _ = _ ++ [op.eval [_, _]]
    rw [ha, hb]
  · change op = .or at hop
    subst op
    simp [step, pointerValue, GateOp.eval]

lemma fold_bounds (n : ℕ) (gs : List Gate) (s : List Gate × List (Option ℕ))
    (hr : validPointers n s.1 s.2) :
    validPointers n (gs.foldl (step n) s).1 (gs.foldl (step n) s).2 := by
  induction gs generalizing s with
  | nil => exact hr
  | cons g gs ih => exact ih (step n s g) (step_bounds n s g hr)

lemma fold_values (n : ℕ) (gs : List Gate) (s : List Gate × List (Option ℕ))
    (hr : validPointers n s.1 s.2) (hgs : ∀ g ∈ gs, allowed g) (x : Fin n → Bool) :
    (gs.foldl (step n) s).2.map (pointerValue (wireValues n (gs.foldl (step n) s).1 x)) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (s.2.map (pointerValue (wireValues n s.1 x))) := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih (step n s g) (step_bounds n s g hr) (fun g' hg' => hgs g' (by simp [hg']))]
      rw [step_values n s g hr (hgs g (by simp)) x]

def initial (n : ℕ) : List Gate × List (Option ℕ) :=
  ([], List.ofFn fun i : Fin n => some i.val)

def compile (n : ℕ) (gs : List Gate) : List Gate × List (Option ℕ) :=
  gs.foldl (step n) (initial n)

lemma initial_bounds (n : ℕ) : validPointers n (initial n).1 (initial n).2 := by
  intro r hr i hi
  simp only [initial, List.mem_ofFn] at hr
  obtain ⟨j,rfl⟩ := hr
  have he : j.val = i := Option.some.inj hi
  simpa [initial, he] using j.isLt

lemma initial_values (n : ℕ) (x : Fin n → Bool) :
    (initial n).2.map (pointerValue (wireValues n (initial n).1 x)) = List.ofFn x := by
  simp only [initial, wireValues, List.foldl_nil, List.map_ofFn]
  congr 1
  funext i
  simp [pointerValue]

lemma compile_values (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, allowed g) (x : Fin n → Bool) :
    (compile n gs).2.map (pointerValue (wireValues n (compile n gs).1 x)) = wireValues n gs x := by
  have h := fold_values n gs (initial n) (initial_bounds n) hgs x
  rw [initial_values] at h
  exact h

lemma compile_size (n : ℕ) (gs : List Gate) : (compile n gs).1.length ≤ binaryCount gs := by
  simpa only [compile, initial, List.length_nil, Nat.zero_add] using fold_size n gs (initial n)

lemma compile_value (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, allowed g)
    (w : ℕ) (x : Fin n → Bool) :
    pointerValue (wireValues n (compile n gs).1 x) ((compile n gs).2.getD w none) =
      (wireValues n gs x).getD w false := by
  have h := List.getD_map (compile n gs).2 none (n := w)
    (pointerValue (wireValues n (compile n gs).1 x))
  change ((compile n gs).2.map (pointerValue (wireValues n (compile n gs).1 x))).getD w false = _ at h
  rw [compile_values n gs hgs x] at h
  exact h.symm

def good (n : ℕ) (gs : List Gate) : Prop :=
  PEqualNP.TopForm.IsAO2 n ⟨gs, 0⟩

lemma good_nil (n : ℕ) : good n [] := by
  simp [good, PEqualNP.TopForm.IsAO2, PEqualNP.EdgeOwnership.AndOrOnly,
    PEqualNP.MetaComplexity.NestedCover.ReadsBack]

lemma good_append (n : ℕ) (gs : List Gate) (op : GateOp) (a b : ℕ)
    (hgs : good n gs) (hop : op = .and ∨ op = .or)
    (ha : a < n + gs.length) (hb : b < n + gs.length) :
    good n (gs ++ [({ op := op, inputs := [a,b] } : Gate)]) := by
  obtain ⟨hops,hback,hbin⟩ := hgs
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hops g hg
    · exact hop
  · intro j hj i hi
    change j < (gs ++ [({ op := op, inputs := [a,b] } : Gate)]).length at hj
    change i ∈ ((gs ++ [({ op := op, inputs := [a,b] } : Gate)]).getD j ⟨.or,[]⟩).inputs at hi
    by_cases hjold : j < gs.length
    · rw [List.getD_append _ _ _ _ hjold] at hi
      exact hback j hjold i hi
    · have heq : j = gs.length := by simp only [List.length_append, List.length_cons, List.length_nil] at hj; omega
      subst j
      simp only [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero,
        List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hbin g hg
    · rfl

lemma emit_good (n : ℕ) (gs : List Gate) (op : GateOp) (a b : Option ℕ)
    (hgs : good n gs) (hop : op = .and ∨ op = .or)
    (ha : bounded n gs a) (hb : bounded n gs b) :
    good n (emit n gs op a b).1 := by
  rcases hop with rfl | rfl
  all_goals cases a <;> cases b <;> simp only [emit]
  all_goals first | exact hgs | exact good_append n gs _ _ _ hgs (by simp) (ha _ rfl) (hb _ rfl)

lemma step_good (n : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate)
    (hgs : good n s.1) (hr : validPointers n s.1 s.2) (hg : allowed g) :
    good n (step n s g).1 := by
  rcases g with ⟨op,ins⟩
  rcases hg with ⟨hop,hlen⟩ | ⟨hop,rfl⟩
  · obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp hlen
    exact emit_good n s.1 op _ _ hgs hop (get_pointer_bound n s.1 s.2 hr a)
      (get_pointer_bound n s.1 s.2 hr b)
  · exact hgs

lemma fold_good (n : ℕ) (gs : List Gate) (s : List Gate × List (Option ℕ))
    (hcode : good n s.1) (hr : validPointers n s.1 s.2) (hgs : ∀ g ∈ gs, allowed g) :
    good n (gs.foldl (step n) s).1 := by
  induction gs generalizing s with
  | nil => exact hcode
  | cons g gs ih =>
      exact ih (step n s g) (step_good n s g hcode hr (hgs g (by simp)))
        (step_bounds n s g hr) (fun g' hg' => hgs g' (by simp [hg']))

lemma compile_good (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, allowed g) :
    good n (compile n gs).1 :=
  fold_good n gs (initial n) (good_nil n) (initial_bounds n) hgs

lemma compiled_circuit (n : ℕ) (C : Circuit) (hgs : ∀ g ∈ C.gates, allowed g)
    (hnonzero : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true) :
    ∃ D : Circuit, D.gates = (compile n C.gates).1 ∧
      PEqualNP.TopForm.IsAO2 n D ∧ D.size ≤ binaryCount C.gates ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hout : ∃ o, (compile n C.gates).2.getD C.output none = some o := by
    cases ho : (compile n C.gates).2.getD C.output none with
    | some o => exact ⟨o,rfl⟩
    | none =>
        obtain ⟨x,hx⟩ := hnonzero
        have h := compile_value n C.gates hgs C.output x
        rw [ho] at h
        change false = C.eval (List.ofFn x) at h
        rw [hx] at h
        contradiction
  obtain ⟨o,ho⟩ := hout
  refine ⟨⟨(compile n C.gates).1,o⟩, rfl, compile_good n C.gates hgs, compile_size n C.gates, ?_⟩
  intro x
  have h := compile_value n C.gates hgs C.output x
  rw [ho] at h
  exact h

lemma compiled_nonzero_wire (n : ℕ) (C D : Circuit) (hgs : ∀ g ∈ C.gates, allowed g)
    (hD : D.gates = (compile n C.gates).1) (w : ℕ)
    (hnonzero : ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = true) :
    ∃ v, ∀ x : Fin n → Bool,
      (D.wires (List.ofFn x)).getD v false = (C.wires (List.ofFn x)).getD w false := by
  have hout : ∃ v, (compile n C.gates).2.getD w none = some v := by
    cases hv : (compile n C.gates).2.getD w none with
    | some v => exact ⟨v,rfl⟩
    | none =>
        obtain ⟨x,hx⟩ := hnonzero
        have h := compile_value n C.gates hgs w x
        rw [hv] at h
        change false = (C.wires (List.ofFn x)).getD w false at h
        rw [hx] at h
        contradiction
  obtain ⟨v,hv⟩ := hout
  refine ⟨v, fun x => ?_⟩
  have h := compile_value n C.gates hgs w x
  rw [hv] at h
  change (wireValues n (compile n C.gates).1 x).getD v false = _ at h
  change (wireValues n D.gates x).getD v false = _
  rw [hD]
  exact h

end PEqualNP.Outside.L_meta_4970_aux.H5Compile


namespace PEqualNP.Outside.L_meta_4970_aux.H5Reach

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.TwoColour

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega

lemma orSets_length (n : ℕ) (C : Circuit) :
    (PEqualNP.CleanedNonEdge.orSets n C).length = C.gates.length := by
  unfold PEqualNP.CleanedNonEdge.orSets
  rw [orSets_len]; simp

lemma orSets_char (n : ℕ) (gs : List Gate) :
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

lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD (w - n) []) := by
  have h := orSets_char n C.gates x k
  unfold PEqualNP.CleanedNonEdge.orSets gateAt
  rw [h]
  constructor
  · rintro ⟨_, h3⟩; exact h3
  · intro h3; exact ⟨hk, h3⟩

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
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

lemma orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) j :=
  (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩

lemma orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C i g) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g :=
  (orReaches_iff n C j g).mpr ⟨hj, Or.inr ⟨hop, i, hi, hlt, h⟩⟩

lemma orReaches_bound (n : ℕ) (C : Circuit) (g : ℕ) :
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

lemma orReaches_trans (n : ℕ) (C : Circuit) (k g : ℕ) (hkg : PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w k → PEqualNP.CleanedNonEdge.OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨m, rfl⟩ : ∃ m, w = n + m := ⟨w - n, by omega⟩
    obtain ⟨hm, h3⟩ := (orReaches_iff n C m k).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]; exact hkg
    · exact orReaches_step n C m i g hm hop hi hlt (ih i hlt hri)

lemma orIn_mem_filter {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

lemma mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  exact ⟨fun h => ((orIn_mem_filter _ _ _ _).1 h).2,
    fun h => (orIn_mem_filter _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

lemma orIn_self (n : ℕ) (C : Circuit) (i : Fin n) : i ∈ PEqualNP.TopForm.orIn n C i :=
  (mem_orIn n C i i).mpr (Or.inl rfl)

lemma orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ PEqualNP.TopForm.orIn n C i) : a ∈ PEqualNP.TopForm.orIn n C (n + j) := by
  rw [mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩


lemma orIn_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    orIn n C w = {⟨w, hw⟩} := by
  ext i
  rw [mem_orIn, Finset.mem_singleton]
  constructor
  · rintro (he | ⟨j, hj, hr, ho, hi⟩)
    · exact Fin.ext he
    · have := hr.1
      omega
  · intro he
    exact Or.inl (congrArg Fin.val he)

lemma orIn_invalid (n : ℕ) (C : Circuit) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : orIn n C w = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro i hi
  rcases (mem_orIn n C w i).mp hi with he | ⟨j, hj, hr, ho, hi⟩
  · have := i.isLt
    omega
  · have := (orReaches_bound n C j w hr).2
    omega

lemma orIn_gate (n : ℕ) (C : Circuit) (hC : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) :
    orIn n C (n + j) = @ite (Finset (Fin n)) ((gateAt C j).op = .or) (Classical.propDecidable _)
      ((gateAt C j).inputs.toFinset.biUnion (orIn n C)) ∅ := by
  classical
  ext a
  rw [mem_orIn]
  by_cases hop : (gateAt C j).op = .or
  · simp only [hop, ↓reduceIte, Finset.mem_biUnion]
    constructor
    · rintro (he | ⟨k, hk, hr, hok, hai⟩)
      · have := a.isLt
        omega
      · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨_, w, hw, hlt, hrw⟩⟩
        · subst k
          exact ⟨a.val, List.mem_toFinset.mpr hai, orIn_self n C a⟩
        · exact ⟨w, List.mem_toFinset.mpr hw,
            (mem_orIn n C w a).mpr (Or.inr ⟨k, hk, hrw, hok, hai⟩)⟩
    · rintro ⟨w, hw, haw⟩
      have hw' := List.mem_toFinset.mp hw
      exact (mem_orIn n C (n+j) a).mp
        (orIn_up n C j w a hj hop hw' (hC j hj w hw') haw)
  · simp only [hop, ↓reduceIte]
    simp only [Finset.notMem_empty, iff_false]
    rintro (he | ⟨k, hk, hr, hok, hai⟩)
    · have := a.isLt
      omega
    · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨ho, _⟩⟩
      · subst k
        exact hop hok
      · exact hop ho

noncomputable def reachFrom {n : ℕ} (gs : List Gate) (w : List (Finset (Fin n))) : List (Finset (Fin n)) := by
  classical
  exact gs.foldl (fun acc g => acc ++ [if g.op = .or then
    g.inputs.toFinset.biUnion (fun i => acc.getD i ∅) else ∅]) w

noncomputable def reachValues (n : ℕ) (gs : List Gate) : List (Finset (Fin n)) :=
  reachFrom gs (List.ofFn fun i : Fin n => {i})

lemma reachFrom_append {n : ℕ} (gs₁ gs₂ : List Gate) (w : List (Finset (Fin n))) :
    reachFrom (gs₁ ++ gs₂) w = reachFrom gs₂ (reachFrom gs₁ w) := by
  simp [reachFrom, List.foldl_append]

lemma reachFrom_ext {n : ℕ} (gs : List Gate) : ∀ w : List (Finset (Fin n)),
    ∃ t : List (Finset (Fin n)), reachFrom gs w = w ++ t ∧ t.length = gs.length := by
  classical
  induction gs with
  | nil => intro w; exact ⟨[], by simp [reachFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := if g.op = .or then g.inputs.toFinset.biUnion (fun i => w.getD i ∅) else ∅
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : reachFrom (g :: gs) w = reachFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma reachFrom_length {n : ℕ} (gs : List Gate) (w : List (Finset (Fin n))) :
    (reachFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := reachFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma reachValues_length (n : ℕ) (gs : List Gate) :
    (reachValues n gs).length = n + gs.length := by
  simp [reachValues, reachFrom_length]

lemma reachValues_append (n : ℕ) (gs : List Gate) (g : Gate) :
    reachValues n (gs ++ [g]) = reachValues n gs ++
      [@ite (Finset (Fin n)) (g.op = .or) (Classical.propDecidable _)
        (g.inputs.toFinset.biUnion (fun i => (reachValues n gs).getD i ∅)) ∅] := by
  classical
  simp [reachValues, reachFrom, List.foldl_append]

lemma getD_reachFrom_lt {n : ℕ} (gs : List Gate) (w : List (Finset (Fin n)))
    (i : ℕ) (hi : i < w.length) :
    (reachFrom gs w).getD i ∅ = w.getD i ∅ := by
  obtain ⟨t, ht, _⟩ := reachFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ hi]

lemma getD_reachFrom_take {n : ℕ} (gs : List Gate) (w : List (Finset (Fin n)))
    (k i : ℕ) (hk : k ≤ gs.length) :
    (reachFrom (gs.take k) w).getD i ∅ =
      if i < w.length + k then (reachFrom gs w).getD i ∅ else ∅ := by
  have hlen : (reachFrom (gs.take k) w).length = w.length + k := by
    rw [reachFrom_length, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, reachFrom_append]
    exact (getD_reachFrom_lt (gs.drop k) (reachFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_reachFrom_gate {n : ℕ} (gs : List Gate) (w : List (Finset (Fin n)))
    (k : ℕ) (hk : k < gs.length) :
    (reachFrom gs w).getD (w.length + k) ∅ =
      @ite (Finset (Fin n)) ((gs[k]).op = .or) (Classical.propDecidable _)
        ((gs[k]).inputs.toFinset.biUnion (fun i =>
          if i < w.length + k then (reachFrom gs w).getD i ∅ else ∅)) ∅ := by
  classical
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (reachFrom (gs.take k) w).length = w.length + k := by
    rw [reachFrom_length, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  let v := if (gs[k]).op = .or then (gs[k]).inputs.toFinset.biUnion
    (fun i => (reachFrom (gs.take k) w).getD i ∅) else ∅
  have heq : reachFrom gs w = reachFrom (gs.drop (k + 1))
      (reachFrom (gs.take k) w ++ [v]) := by
    conv_lhs => rw [hsplit, reachFrom_append]
    rfl
  rw [heq, getD_reachFrom_lt]
  · rw [← hlen]
    have hs : (reachFrom (gs.take k) w ++ [v]).getD (reachFrom (gs.take k) w).length ∅ = v := by simp
    rw [hs]
    unfold v
    split_ifs with hop
    · apply Finset.biUnion_congr rfl
      intro i hi
      rw [getD_reachFrom_take gs w k i (Nat.le_of_lt hk), heq, hlen]
      simp only [v, hop, ↓reduceIte]
    · rfl
  · rw [List.length_append, hlen]
    simp

lemma reachValues_input (n : ℕ) (gs : List Gate) (w : ℕ) (hw : w < n) :
    (reachValues n gs).getD w ∅ = {⟨w, hw⟩} := by
  unfold reachValues
  rw [getD_reachFrom_lt _ _ _ (by simpa using hw)]
  rw [List.getD_eq_getElem _ _ (by simpa using hw)]
  simp

lemma reachValues_gate (n : ℕ) (C : Circuit) (hC : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) :
    (reachValues n C.gates).getD (n+j) ∅ =
      @ite (Finset (Fin n)) ((gateAt C j).op = .or) (Classical.propDecidable _)
        ((gateAt C j).inputs.toFinset.biUnion (fun i => (reachValues n C.gates).getD i ∅)) ∅ := by
  classical
  have he := getD_reachFrom_gate C.gates (List.ofFn fun i : Fin n => {i}) j hj
  simp only [List.length_ofFn] at he
  have hg : gateAt C j = C.gates[j] := by simp [gateAt, hj]
  unfold reachValues
  rw [he, ← hg]
  split_ifs with hop
  · apply Finset.biUnion_congr rfl
    intro i hi
    simp only [hC j hj i (List.mem_toFinset.mp hi), ↓reduceIte]
  · rfl

lemma reachValues_eq_orIn (n : ℕ) (C : Circuit) (hC : ReadsBack n C) :
    ∀ w, (reachValues n C.gates).getD w ∅ = orIn n C w := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hi : w < n
    · rw [reachValues_input n C.gates w hi, orIn_input n C w hi]
    · by_cases hw : w < n + C.gates.length
      · have hj : w-n < C.gates.length := by omega
        have he : n+(w-n) = w := by omega
        rw [← he, reachValues_gate n C hC (w-n) hj, orIn_gate n C hC (w-n) hj]
        split_ifs with hop
        · apply Finset.biUnion_congr rfl
          intro i hmem
          exact ih i (by have := hC (w-n) hj i (List.mem_toFinset.mp hmem); omega)
        · rfl
      · rw [List.getD_eq_default _ _ (by rw [reachValues_length]; omega),
          orIn_invalid n C w (by omega)]

lemma tCount_zero_iff_gate (n : ℕ) (C : Circuit) (lin : ℕ → Bool) :
    tCount n C lin = 0 ↔ ∀ j < C.gates.length, (gateAt C j).op = .or →
      ∀ a ∈ orIn n C (n+j), ∀ b ∈ orIn n C (n+j), lin a.val = lin b.val := by
  classical
  rw [tCount, Finset.card_eq_zero]
  constructor
  · intro hz j hj hop a ha b hb
    by_contra hne
    have hm : (∃ i ∈ orIn n C (n+j), lin i.val = false) ∧
        (∃ i ∈ orIn n C (n+j), lin i.val = true) := by
      cases hla : lin a.val <;> cases hlb : lin b.val
      · exact (hne (hla.trans hlb.symm)).elim
      · exact ⟨⟨a,ha,hla⟩,⟨b,hb,hlb⟩⟩
      · exact ⟨⟨b,hb,hlb⟩,⟨a,ha,hla⟩⟩
      · exact (hne (hla.trans hlb.symm)).elim
    have hmem : j ∈ twoColour n C lin :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hj, hop, hm⟩
    rw [hz] at hmem
    exact Finset.notMem_empty j hmem
  · intro h
    apply Finset.eq_empty_of_forall_notMem
    intro j hj
    obtain ⟨_, hj', hop, ⟨a,ha,hla⟩, ⟨b,hb,hlb⟩⟩ := Finset.mem_filter.mp hj
    have he := h j hj' hop a ha b hb
    rw [hla, hlb] at he
    cases he

lemma tCount_zero_all_wires (n : ℕ) (C : Circuit) (lin : ℕ → Bool)
    (hC : ReadsBack n C) (hT : tCount n C lin = 0) :
    ∀ w, ∀ a ∈ orIn n C w, ∀ b ∈ orIn n C w, lin a.val = lin b.val := by
  classical
  intro w a ha b hb
  by_cases hw : w < n
  · rw [orIn_input n C w hw, Finset.mem_singleton] at ha hb
    rw [ha, hb]
  · by_cases hv : w < n+C.gates.length
    · have hj : w-n < C.gates.length := by omega
      have he : n+(w-n) = w := by omega
      by_cases hop : (gateAt C (w-n)).op = .or
      · exact (tCount_zero_iff_gate n C lin).mp hT (w-n) hj hop a
          (by simpa [he] using ha) b (by simpa [he] using hb)
      · have hempty : orIn n C w = ∅ := by
          rw [← he, orIn_gate n C hC (w-n) hj]
          simp only [hop, ↓reduceIte]
        rw [hempty] at ha
        exact (Finset.notMem_empty a ha).elim
    · rw [orIn_invalid n C w (by omega)] at ha
      exact (Finset.notMem_empty a ha).elim

lemma tCount_zero_iff_reachValues (n : ℕ) (C : Circuit) (lin : ℕ → Bool)
    (hC : ReadsBack n C) :
    tCount n C lin = 0 ↔ ∀ w, ∀ a ∈ (reachValues n C.gates).getD w ∅,
      ∀ b ∈ (reachValues n C.gates).getD w ∅, lin a.val = lin b.val := by
  simp only [reachValues_eq_orIn n C hC]
  constructor
  · exact tCount_zero_all_wires n C lin hC
  · intro h
    exact (tCount_zero_iff_gate n C lin).mpr (fun j hj hop => h (n+j))

lemma tCount_zero_of_orIn_subsets (n : ℕ) (C D : Circuit) (lin : ℕ → Bool)
    (hC : ReadsBack n C) (hT : tCount n C lin = 0)
    (hsub : ∀ j < D.gates.length, (gateAt D j).op = .or →
      ∃ w, orIn n D (n+j) ⊆ orIn n C w) :
    tCount n D lin = 0 := by
  apply (tCount_zero_iff_gate n D lin).mpr
  intro j hj hop a ha b hb
  obtain ⟨w, hw⟩ := hsub j hj hop
  exact tCount_zero_all_wires n C lin hC hT w a (hw ha) b (hw hb)

lemma erased_readsBack (n : ℕ) (C D : Circuit) (hC : ReadsBack n C)
    (hlen : D.gates.length = C.gates.length)
    (hg : ∀ j < C.gates.length, gateAt D j = gateAt C j ∨ gateAt D j = ⟨.or,[]⟩) :
    ReadsBack n D := by
  intro j hj i hi
  have hjC : j < C.gates.length := by omega
  rcases hg j hjC with he | he
  · rw [he] at hi
    exact hC j hjC i hi
  · rw [he] at hi
    simp at hi

lemma erased_orIn_subset (n : ℕ) (C D : Circuit) (hC : ReadsBack n C)
    (hlen : D.gates.length = C.gates.length)
    (hg : ∀ j < C.gates.length, gateAt D j = gateAt C j ∨ gateAt D j = ⟨.or,[]⟩) :
    ∀ w, orIn n D w ⊆ orIn n C w := by
  classical
  have hD := erased_readsBack n C D hC hlen hg
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hw : w < n
    · rw [orIn_input n C w hw, orIn_input n D w hw]
    · by_cases hv : w < n+C.gates.length
      · have hj : w-n < C.gates.length := by omega
        have hjD : w-n < D.gates.length := by omega
        have he : n+(w-n) = w := by omega
        rw [← he, orIn_gate n C hC (w-n) hj, orIn_gate n D hD (w-n) hjD]
        rcases hg (w-n) hj with hsame | hzero
        · rw [hsame]
          split_ifs with hop
          · intro a ha
            obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp ha
            exact Finset.mem_biUnion.mpr ⟨i, hi, ih i
              (by have := hC (w-n) hj i (List.mem_toFinset.mp hi); omega) hai⟩
          · exact Finset.Subset.refl _
        · rw [hzero]
          simp
      · rw [orIn_invalid n D w (by omega)]
        exact Finset.empty_subset _

lemma erased_tCount_zero (n : ℕ) (C D : Circuit) (lin : ℕ → Bool)
    (hC : ReadsBack n C) (hT : tCount n C lin = 0)
    (hlen : D.gates.length = C.gates.length)
    (hg : ∀ j < C.gates.length, gateAt D j = gateAt C j ∨ gateAt D j = ⟨.or,[]⟩) :
    tCount n D lin = 0 := by
  apply tCount_zero_of_orIn_subsets n C D lin hC hT
  intro j hj hop
  exact ⟨n+j, erased_orIn_subset n C D hC hlen hg (n+j)⟩

end PEqualNP.Outside.L_meta_4970_aux.H5Reach

namespace PEqualNP.Outside.L_meta_4970_aux.H5CompileReach
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4970_aux.H5Compile
open H5Reach

noncomputable def gateReach {n : ℕ} (w : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) := by
  classical
  exact if g.op = GateOp.or then g.inputs.toFinset.biUnion (fun i => w.getD i ∅) else ∅

def opReach {n : ℕ} (op : GateOp) (a b : Finset (Fin n)) : Finset (Fin n) :=
  match op with
  | .or => a ∪ b
  | _ => ∅

lemma reachValues_length (n : ℕ) (gs : List Gate) :
    (reachValues n gs).length = n + gs.length := by
  classical
  suffices h : ∀ gs : List Gate, ∀ w : List (Finset (Fin n)),
      (reachFrom gs w).length = w.length + gs.length by
    simpa [reachValues] using h gs (List.ofFn fun i : Fin n => {i})
  intro gs
  induction gs with
  | nil => simp [reachFrom]
  | cons g gs ih =>
    intro w
    simpa [reachFrom, List.foldl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (w ++ [if g.op = GateOp.or then g.inputs.toFinset.biUnion (fun i => w.getD i ∅) else ∅])

lemma reachValues_append (n : ℕ) (gs : List Gate) (g : Gate) :
    reachValues n (gs ++ [g]) = reachValues n gs ++ [gateReach (reachValues n gs) g] := by
  classical
  simp [reachValues, reachFrom, gateReach, List.foldl_append]

def pointerReach {n : ℕ} (w : List (Finset (Fin n))) (r : Option ℕ) : Finset (Fin n) :=
  match r with
  | none => ∅
  | some i => w.getD i ∅

lemma pointerReach_append (n : ℕ) (gs : List Gate) (g : Gate) (r : Option ℕ)
    (hr : bounded n gs r) :
    pointerReach (reachValues n (gs ++ [g])) r = pointerReach (reachValues n gs) r := by
  classical
  cases r with
  | none => rfl
  | some i =>
      simp only [pointerReach, reachValues_append]
      apply List.getD_append
      rw [reachValues_length]
      exact hr i rfl

lemma emit_preserves_reach (n : ℕ) (gs : List Gate) (op : GateOp) (a b r : Option ℕ)
    (hr : bounded n gs r) :
    pointerReach (reachValues n (emit n gs op a b).1) r = pointerReach (reachValues n gs) r := by
  cases a <;> cases b <;> cases op <;> simp only [emit]
  all_goals exact pointerReach_append n gs _ r hr

lemma emit_reach (n : ℕ) (gs : List Gate) (op : GateOp) (a b : Option ℕ)
    (hop : op = .and ∨ op = .or) :
    pointerReach (reachValues n (emit n gs op a b).1) (emit n gs op a b).2 =
      opReach op (pointerReach (reachValues n gs) a) (pointerReach (reachValues n gs) b) := by
  classical
  rcases hop with rfl | rfl
  all_goals cases a <;> cases b <;> simp only [emit, pointerReach, reachValues_append]
  all_goals simp [opReach, gateReach]
  all_goals rw [← reachValues_length n gs]
  all_goals simp

lemma step_reaches (n : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate)
    (hr : validPointers n s.1 s.2) (hg : allowed g) :
    (step n s g).2.map (pointerReach (reachValues n (step n s g).1)) =
      s.2.map (pointerReach (reachValues n s.1)) ++
        [gateReach (s.2.map (pointerReach (reachValues n s.1))) g] := by
  classical
  rcases g with ⟨op,ins⟩
  rcases hg with ⟨hop,hlen⟩ | ⟨hop,rfl⟩
  · obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp hlen
    simp only [step, List.map_append, List.map_cons, List.map_nil]
    have hm : List.map (pointerReach (reachValues n (emit n s.1 op (s.2.getD a none)
        (s.2.getD b none)).1)) s.2 = List.map (pointerReach (reachValues n s.1)) s.2 := by
      apply List.map_congr_left
      intro r hmem
      exact emit_preserves_reach n s.1 op _ _ r (hr r hmem)
    rw [hm, emit_reach n s.1 op _ _ hop]
    have ha := List.getD_map s.2 none (n := a) (pointerReach (reachValues n s.1))
    have hb := List.getD_map s.2 none (n := b) (pointerReach (reachValues n s.1))
    change (s.2.map (pointerReach (reachValues n s.1))).getD a ∅ = _ at ha
    change (s.2.map (pointerReach (reachValues n s.1))).getD b ∅ = _ at hb
    simp only [gateReach, List.toFinset_cons, List.toFinset_nil, Finset.biUnion_insert, Finset.biUnion_empty, Finset.union_empty]
    rw [ha, hb]
    rcases hop with rfl | rfl <;> simp [opReach]
  · change op = .or at hop
    subst op
    simp [step, pointerReach, gateReach]

lemma fold_reaches (n : ℕ) (gs : List Gate) (s : List Gate × List (Option ℕ))
    (hr : validPointers n s.1 s.2) (hgs : ∀ g ∈ gs, allowed g) :
    (gs.foldl (step n) s).2.map (pointerReach (reachValues n (gs.foldl (step n) s).1)) =
      reachFrom gs (s.2.map (pointerReach (reachValues n s.1))) := by
  classical
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih (step n s g) (step_bounds n s g hr) (fun g' hg' => hgs g' (by simp [hg']))]
      rw [step_reaches n s g hr (hgs g (by simp))]
      rfl

lemma initial_reaches (n : ℕ) :
    (initial n).2.map (pointerReach (reachValues n (initial n).1)) =
      List.ofFn fun i : Fin n => {i} := by
  simp only [initial, reachValues, reachFrom, List.foldl_nil, List.map_ofFn]
  congr 1
  funext i
  simp [pointerReach]

lemma compile_reaches (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, allowed g) :
    (compile n gs).2.map (pointerReach (reachValues n (compile n gs).1)) = reachValues n gs := by
  have h := fold_reaches n gs (initial n) (initial_bounds n) hgs
  rw [initial_reaches] at h
  exact h

lemma compile_reach (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, allowed g) (w : ℕ) :
    pointerReach (reachValues n (compile n gs).1) ((compile n gs).2.getD w none) =
      (reachValues n gs).getD w ∅ := by
  have h := List.getD_map (compile n gs).2 none (n := w)
    (pointerReach (reachValues n (compile n gs).1))
  change ((compile n gs).2.map (pointerReach (reachValues n (compile n gs).1))).getD w ∅ = _ at h
  rw [compile_reaches n gs hgs] at h
  exact h.symm

def covered (n : ℕ) (gs : List Gate) (rs : List (Option ℕ)) : Prop :=
  ∀ i < n + gs.length, some i ∈ rs

lemma emit_covered (n : ℕ) (gs : List Gate) (rs : List (Option ℕ))
    (op : GateOp) (a b : Option ℕ) (hr : covered n gs rs) :
    covered n (emit n gs op a b).1 (rs ++ [(emit n gs op a b).2]) := by
  intro i hi
  cases a <;> cases b <;> cases op <;> simp only [emit, List.length_append,
    List.length_cons, List.length_nil] at hi ⊢
  all_goals by_cases hlt : i < n + gs.length
  all_goals try exact List.mem_append_left _ (hr i hlt)
  all_goals try omega
  all_goals have heq : i = n + gs.length := by omega
  all_goals subst i
  all_goals exact List.mem_append_right _ (by simp)

lemma step_covered (n : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate)
    (hr : covered n s.1 s.2) : covered n (step n s g).1 (step n s g).2 := by
  rcases g with ⟨op,ins⟩
  cases ins with
  | nil =>
      intro i hi
      exact List.mem_append_left _ (hr i hi)
  | cons a ins =>
      cases ins with
      | nil =>
          intro i hi
          exact List.mem_append_left _ (hr i hi)
      | cons b ins =>
          cases ins with
          | cons c ins =>
              intro i hi
              exact List.mem_append_left _ (hr i hi)
          | nil => exact emit_covered n s.1 s.2 op (s.2.getD a none) (s.2.getD b none) hr

lemma fold_covered (n : ℕ) (gs : List Gate) (s : List Gate × List (Option ℕ))
    (hr : covered n s.1 s.2) :
    covered n (gs.foldl (step n) s).1 (gs.foldl (step n) s).2 := by
  induction gs generalizing s with
  | nil => exact hr
  | cons g gs ih => exact ih (step n s g) (step_covered n s g hr)

lemma initial_covered (n : ℕ) : covered n (initial n).1 (initial n).2 := by
  intro i hi
  change i < n + 0 at hi
  change some i ∈ List.ofFn (fun i : Fin n => some i.val)
  exact List.mem_ofFn.mpr ⟨⟨i, by omega⟩, rfl⟩

lemma compile_covered (n : ℕ) (gs : List Gate) :
    covered n (compile n gs).1 (compile n gs).2 :=
  fold_covered n gs (initial n) (initial_covered n)

lemma compiled_reach_mem_source (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, allowed g) (R : Finset (Fin n))
    (hR : R ∈ reachValues n (compile n gs).1) : R ∈ reachValues n gs := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hR
  have hic : i < n + (compile n gs).1.length := by
    simpa only [reachValues_length] using hi
  have himem := compile_covered n gs i hic
  have hv : pointerReach (reachValues n (compile n gs).1) (some i) =
      (reachValues n (compile n gs).1)[i] := by
    exact List.getD_eq_getElem _ _ hi
  have hmem : pointerReach (reachValues n (compile n gs).1) (some i) ∈
      (compile n gs).2.map (pointerReach (reachValues n (compile n gs).1)) := by
    exact List.mem_map.mpr ⟨some i, himem, rfl⟩
  rw [compile_reaches n gs hgs, hv] at hmem
  exact hmem

lemma compile_preserves_reach_property (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, allowed g) (P : Finset (Fin n) → Prop)
    (hP : ∀ R ∈ reachValues n gs, P R) :
    ∀ R ∈ reachValues n (compile n gs).1, P R := by
  intro R hR
  exact hP R (compiled_reach_mem_source n gs hgs R hR)

lemma compile_monochromatic (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, allowed g) (color : Fin n → Bool)
    (hmono : ∀ R ∈ reachValues n gs, ∀ a ∈ R, ∀ b ∈ R, color a = color b) :
    ∀ R ∈ reachValues n (compile n gs).1,
      ∀ a ∈ R, ∀ b ∈ R, color a = color b :=
  compile_preserves_reach_property n gs hgs _ hmono

lemma compile_monochromatic_at (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, allowed g) (color : Fin n → Bool)
    (hmono : ∀ w, ∀ a ∈ (reachValues n gs).getD w ∅,
      ∀ b ∈ (reachValues n gs).getD w ∅, color a = color b) :
    ∀ w, ∀ a ∈ (reachValues n (compile n gs).1).getD w ∅,
      ∀ b ∈ (reachValues n (compile n gs).1).getD w ∅, color a = color b := by
  have hm : ∀ R ∈ reachValues n gs, ∀ a ∈ R, ∀ b ∈ R, color a = color b := by
    intro R hR
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hR
    simpa only [List.getD_eq_getElem _ _ hi] using hmono i
  have hc := compile_monochromatic n gs hgs color hm
  intro w a ha b hb
  by_cases hw : w < (reachValues n (compile n gs).1).length
  · rw [List.getD_eq_getElem _ _ hw] at ha hb
    exact hc _ (List.getElem_mem hw) a ha b hb
  · rw [List.getD_eq_default _ _ (by omega)] at ha
    simp at ha

lemma compile_tCount_zero (n : ℕ) (C : Circuit) (lin : ℕ → Bool)
    (hgs : ∀ g ∈ C.gates, allowed g)
    (hback : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (hzero : PEqualNP.TwoColour.tCount n C lin = 0) (o : ℕ) :
    PEqualNP.TwoColour.tCount n ⟨(compile n C.gates).1, o⟩ lin = 0 := by
  have hgood := compile_good n C.gates hgs
  apply (H5Reach.tCount_zero_iff_reachValues n ⟨(compile n C.gates).1, o⟩ lin hgood.2.1).mpr
  exact compile_monochromatic_at n C.gates hgs (fun i => lin i.val)
    ((H5Reach.tCount_zero_iff_reachValues n C lin hback).mp hzero)

lemma compiled_tCount_zero (n : ℕ) (C D : Circuit) (lin : ℕ → Bool)
    (hgs : ∀ g ∈ C.gates, allowed g)
    (hback : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (hzero : PEqualNP.TwoColour.tCount n C lin = 0)
    (hD : D.gates = (compile n C.gates).1) :
    PEqualNP.TwoColour.tCount n D lin = 0 := by
  rcases D with ⟨gs, o⟩
  change gs = (compile n C.gates).1 at hD
  subst gs
  exact compile_tCount_zero n C lin hgs hback hzero o

end PEqualNP.Outside.L_meta_4970_aux.H5CompileReach


namespace PEqualNP.Outside.L_meta_4970_aux.H5Bridge

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open H5Pruning H5Compile

lemma zeroed_allowed (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (j : ℕ) :
    ∀ g ∈ (zeroed C j).gates, allowed g := by
  intro g hg
  change g ∈ C.gates.take j ++ ⟨GateOp.or,[]⟩ :: C.gates.drop (j+1) at hg
  rcases List.mem_append.mp hg with hg | hg
  · have hm := List.mem_of_mem_take hg
    exact Or.inl ⟨hC.1 g hm, hC.2.2 g hm⟩
  · rcases List.mem_cons.mp hg with rfl | hg
    · exact Or.inr ⟨rfl,rfl⟩
    · have hm := List.mem_of_mem_drop hg
      exact Or.inl ⟨hC.1 g hm, hC.2.2 g hm⟩

lemma zeroed_binaryCount_lt (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    binaryCount (zeroed C j).gates < C.size := by
  have ht := List.countP_le_length (l := C.gates.take j) (p := fun g : Gate => g.inputs.length == 2)
  have hd := List.countP_le_length (l := C.gates.drop (j+1)) (p := fun g : Gate => g.inputs.length == 2)
  simp only [List.length_take, List.length_drop] at ht hd
  have hm : min j C.gates.length = j := Nat.min_eq_left (by omega)
  rw [hm] at ht
  simp [binaryCount, zeroed, Circuit.size]
  omega

lemma compiled_star (n : ℕ) (C D : Circuit) (hgs : ∀ g ∈ C.gates, allowed g)
    (hD : D.gates = (compile n C.gates).1) (hAO : IsAO2 n D)
    (Q : Finset (Fin n)) (hQ : 2 ≤ Q.card) (w : ℕ)
    (hspec : ∀ x, wireFn n C w x = starFun Q x) :
    ∃ j < D.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = GateOp.or ∧
      ∀ x, wireFn n D (n+j) x = starFun Q x := by
  obtain ⟨q,hq⟩ := Finset.card_pos.mp (show 0 < Q.card by omega)
  have hp : ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = true := by
    refine ⟨fun _ => true, ?_⟩
    change wireFn n C w (fun _ => true) = true
    rw [hspec]
    exact decide_eq_true ⟨q,hq,rfl⟩
  obtain ⟨v,hv⟩ := compiled_nonzero_wire n C D hgs hD w hp
  apply pure_star_or_root n D hAO Q hQ v
  intro x
  exact (hv x).trans (hspec x)

lemma prune_bipartite_output {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : E.Nonempty) (C : Circuit) (hC : IsAO2 (p+l) C)
    (j : ℕ) (hj : j < C.gates.length)
    (hzero : ∀ a b, (a,b) ∈ E →
      wireFn (p+l) C (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = false)
    (hspec : ∀ x : Fin (p+l) → Bool,
      PEqualNP.MetaComplexity.circuitFun (p+l) C x =
        decide (∃ (a : Fin p) (b : Fin l), (a,b) ∈ E ∧
          x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    ∃ D : Circuit, D.gates = (compile (p+l) (zeroed C j).gates).1 ∧
      IsAO2 (p+l) D ∧ D.size < C.size ∧
      ∀ x : Fin (p+l) → Bool,
        PEqualNP.MetaComplexity.circuitFun (p+l) D x =
          decide (∃ (a : Fin p) (b : Fin l), (a,b) ∈ E ∧
            x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true) := by
  have hz := zeroed_bipartite_output_preserved E C hC j hj hzero hspec
  have hn : ∃ x : Fin (p+l) → Bool, (zeroed C j).eval (List.ofFn x) = true := by
    refine ⟨fun _ => true, ?_⟩
    change PEqualNP.MetaComplexity.circuitFun (p+l) (zeroed C j) (fun _ => true) = true
    rw [hz]
    obtain ⟨⟨a,b⟩,hab⟩ := hE
    exact decide_eq_true ⟨a,b,hab,rfl,rfl⟩
  obtain ⟨D,hcode,hAO,hsize,hev⟩ := compiled_circuit (p+l) (zeroed C j) (zeroed_allowed _ C hC j) hn
  refine ⟨D,hcode,hAO,lt_of_le_of_lt hsize (zeroed_binaryCount_lt C j hj), ?_⟩
  intro x
  exact (hev x).trans (hz x)

def served (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit) : Prop :=
  ∀ (a : Fin p) (b : Fin l), (a,b) ∈ E →
    (∃ (j : ℕ) (Q : Finset (Fin l)), j < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or ∧
      2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, (a,b') ∈ E) ∧
      ∀ x : Fin (p+l) → Bool, (C.wires (List.ofFn x)).getD (p+l+j) false =
        decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) ∨
    (∃ (j : ℕ) (P : Finset (Fin p)), j < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or ∧
      2 ≤ P.card ∧ a ∈ P ∧ (∀ a' ∈ P, (a',b) ∈ E) ∧
      ∀ x : Fin (p+l) → Bool, (C.wires (List.ofFn x)).getD (p+l+j) false =
        decide (∃ a' ∈ P, x (Fin.castAdd l a') = true))

lemma prune_served {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C D : Circuit) (hC : IsAO2 (p+l) C) (hD : IsAO2 (p+l) D)
    (j : ℕ) (hj : j < C.gates.length)
    (hcode : D.gates = (compile (p+l) (zeroed C j).gates).1)
    (hzero : ∀ a b, (a,b) ∈ E →
      wireFn (p+l) C (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = false)
    (hs : served p l E C) : served p l E D := by
  intro a b hab
  rcases hs a b hab with ⟨k,Q,hk,hop,hQ,hb,hsub,hval⟩ | ⟨k,P,hk,hop,hP,ha,hsub,hval⟩
  · left
    have hinj : Function.Injective (Fin.natAdd p : Fin l → Fin (p+l)) := by
      intro b b' h
      apply Fin.ext
      have hh := congrArg Fin.val h
      simp only [Fin.val_natAdd] at hh
      omega
    let Q' := Q.image (Fin.natAdd p)
    have hc : 2 ≤ Q'.card := by rw [Finset.card_image_of_injective _ hinj]; exact hQ
    have hz := zeroed_left_star_preserved E a Q hsub C hC j hj hzero (p+l+k) hval
    have hz' : ∀ x, wireFn (p+l) (zeroed C j) (p+l+k) x = starFun Q' x := by
      intro x
      simpa [starFun,Q'] using hz x
    obtain ⟨k',hk',hop',hval'⟩ := compiled_star (p+l) (zeroed C j) D
      (zeroed_allowed _ C hC j) hcode hD Q' hc (p+l+k) hz'
    refine ⟨k',Q,hk',hop',hQ,hb,hsub,?_⟩
    intro x
    simpa [starFun,Q',wireFn] using hval' x
  · right
    have hinj : Function.Injective (Fin.castAdd l : Fin p → Fin (p+l)) := by
      intro a a' h
      apply Fin.ext
      exact congrArg (fun i : Fin (p+l) => i.val) h
    let P' := P.image (Fin.castAdd l)
    have hc : 2 ≤ P'.card := by rw [Finset.card_image_of_injective _ hinj]; exact hP
    have hz := zeroed_right_star_preserved E b P hsub C hC j hj hzero (p+l+k) hval
    have hz' : ∀ x, wireFn (p+l) (zeroed C j) (p+l+k) x = starFun P' x := by
      intro x
      simpa [starFun,P'] using hz x
    obtain ⟨k',hk',hop',hval'⟩ := compiled_star (p+l) (zeroed C j) D
      (zeroed_allowed _ C hC j) hcode hD P' hc (p+l+k) hz'
    refine ⟨k',P,hk',hop',hP,ha,hsub,?_⟩
    intro x
    simpa [starFun,P',wireFn] using hval' x

lemma prune_bipartite_served {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : E.Nonempty) (C : Circuit) (hC : IsAO2 (p+l) C)
    (j : ℕ) (hj : j < C.gates.length)
    (hzero : ∀ a b, (a,b) ∈ E →
      wireFn (p+l) C (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = false)
    (hspec : ∀ x : Fin (p+l) → Bool,
      PEqualNP.MetaComplexity.circuitFun (p+l) C x =
        decide (∃ (a : Fin p) (b : Fin l), (a,b) ∈ E ∧
          x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (hs : served p l E C) :
    ∃ D : Circuit, IsAO2 (p+l) D ∧ D.size < C.size ∧ served p l E D ∧
      ∀ x : Fin (p+l) → Bool,
        PEqualNP.MetaComplexity.circuitFun (p+l) D x =
          decide (∃ (a : Fin p) (b : Fin l), (a,b) ∈ E ∧
            x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true) := by
  obtain ⟨D,hcode,hD,hsize,hval⟩ := prune_bipartite_output E hE C hC j hj hzero hspec
  exact ⟨D,hD,hsize,prune_served E C D hC hD j hj hcode hzero hs,hval⟩

end PEqualNP.Outside.L_meta_4970_aux.H5Bridge


namespace PEqualNP.Outside.L_meta_4970_aux.H5Bridge

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TwoColour
open H5Pruning H5Compile H5Reach H5CompileReach

lemma take_cons_drop_set (gs : List Gate) (j : ℕ) (g : Gate) (hj : j < gs.length) :
    gs.take j ++ g :: gs.drop (j+1) = gs.set j g := by
  induction gs generalizing j with
  | nil => simp at hj
  | cons a gs ih =>
      cases j with
      | zero => rfl
      | succ j =>
          simpa using congrArg (List.cons a) (ih j (by simpa using hj))

lemma zeroed_gates_set (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (zeroed C j).gates = C.gates.set j ⟨.or,[]⟩ :=
  take_cons_drop_set C.gates j _ hj

lemma zeroed_length (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (zeroed C j).gates.length = C.gates.length := by
  rw [zeroed_gates_set C j hj]
  exact List.length_set

lemma zeroed_gateAt (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (i : ℕ) (hi : i < C.gates.length) :
    gateAt (zeroed C j) i = gateAt C i ∨ gateAt (zeroed C j) i = ⟨.or,[]⟩ := by
  unfold gateAt
  rw [zeroed_gates_set C j hj]
  by_cases h : i = j
  · subst i
    right
    simp [hj]
  · left
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]
    exact List.getElem_set_ne (Ne.symm h) _

lemma zeroed_readsBack (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hC : ReadsBack n C) : ReadsBack n (zeroed C j) := by
  intro i hi w hw
  have hi' : i < C.gates.length := by simpa [zeroed_length C j hj] using hi
  rcases zeroed_gateAt C j hj i hi' with hg | hg
  · rw [hg] at hw
    exact hC i hi' w hw
  · rw [hg] at hw
    simp at hw

lemma zeroed_tCount (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hC : ReadsBack n C) (lin : ℕ → Bool) (hT : tCount n C lin = 0) :
    tCount n (zeroed C j) lin = 0 :=
  erased_tCount_zero n C (zeroed C j) lin hC hT (zeroed_length C j hj)
    (zeroed_gateAt C j hj)

def computes (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit) : Prop :=
  ∀ x : Fin (p+l) → Bool,
    PEqualNP.MetaComplexity.circuitFun (p+l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a,b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)

def admissible (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit) : Prop :=
  IsAO2 (p+l) C ∧ computes p l E C ∧
    tCount (p+l) C (fun i => decide (p ≤ i)) = 0 ∧ served p l E C

lemma prune_admissible {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : E.Nonempty) (C : Circuit) (hC : admissible p l E C)
    (j : ℕ) (hj : j < C.gates.length)
    (hzero : ∀ a b, (a,b) ∈ E →
      wireFn (p+l) C (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = false) :
    ∃ D : Circuit, admissible p l E D ∧ D.size < C.size := by
  obtain ⟨hAO,hfun,hT,hs⟩ := hC
  obtain ⟨D,hcode,hD,hsize,hval⟩ := prune_bipartite_output E hE C hAO j hj hzero hfun
  have hTs : tCount (p+l) (zeroed C j) (fun i => decide (p ≤ i)) = 0 :=
    zeroed_tCount (p+l) C j hj hAO.2.1 _ hT
  have hTD : tCount (p+l) D (fun i => decide (p ≤ i)) = 0 :=
    compiled_tCount_zero (p+l) (zeroed C j) D _ (zeroed_allowed _ C hAO j)
      (zeroed_readsBack _ C j hj hAO.2.1) hTs hcode
  exact ⟨D,⟨hD,hval,hTD,prune_served E C D hAO hD j hj hcode hzero hs⟩,hsize⟩

lemma exists_edge_active {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : E.Nonempty) (C : Circuit) (hC : admissible p l E C) :
    ∃ D : Circuit, admissible p l E D ∧ D.size ≤ C.size ∧
      ∀ j < D.gates.length, ∃ (a : Fin p) (b : Fin l), (a,b) ∈ E ∧
        wireFn (p+l) D (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true := by
  classical
  have hex : ∃ m : ℕ, ∃ D : Circuit, admissible p l E D ∧ D.size = m :=
    ⟨C.size,C,hC,rfl⟩
  obtain ⟨D,hD,hm⟩ := Nat.find_spec hex
  have hle : Nat.find hex ≤ C.size := Nat.find_min' hex ⟨C,hC,rfl⟩
  refine ⟨D,hD,by omega,?_⟩
  intro j hj
  by_contra hbad
  have hzero : ∀ a b, (a,b) ∈ E →
      wireFn (p+l) D (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = false := by
    intro a b hab
    cases hv : wireFn (p+l) D (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) with
    | false => rfl
    | true => exact False.elim (hbad ⟨a,b,hab,hv⟩)
  obtain ⟨D',hD',hlt⟩ := prune_admissible E hE D hD j hj hzero
  have hle' : Nat.find hex ≤ D'.size := Nat.find_min' hex ⟨D',hD',rfl⟩
  omega

end PEqualNP.Outside.L_meta_4970_aux.H5Bridge


namespace PEqualNP.Outside.L_meta_4970_aux.H5Deletion

def residual {p l : ℕ} (E : Finset (Fin p × Fin l)) (v : Fin l) :
    Finset (Fin p × Fin l) :=
  E.filter fun e => (e.1, v) ∈ E ∧ e.2 ≠ v

lemma residual_right_injective {p l : ℕ} (E : Finset (Fin p × Fin l)) (v : Fin l)
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) :
    Set.InjOn Prod.snd (residual E v : Set (Fin p × Fin l)) := by
  intro x hx y hy hxy
  obtain ⟨a, b⟩ := x
  obtain ⟨a', b'⟩ := y
  change b = b' at hxy
  subst b'
  have hx' := Finset.mem_filter.mp hx
  have hy' := Finset.mem_filter.mp hy
  have haa : a = a' := by
    by_contra hne
    exact hfour a a' b v hne hx'.2.2 ⟨hx'.1, hx'.2.1, hy'.1, hy'.2.1⟩
  subst a'
  rfl

lemma residual_card {p l : ℕ} (E : Finset (Fin p × Fin l)) (v : Fin l)
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) :
    (residual E v).card = ((residual E v).image Prod.snd).card := by
  symm
  exact Finset.card_image_iff.mpr (residual_right_injective E v hfour)

def endpoints {p l : ℕ} (E : Finset (Fin p × Fin l)) : Finset (Fin (p + l)) :=
  (E.image fun e => Fin.castAdd l e.1) ∪ (E.image fun e => Fin.natAdd p e.2)

def leftCover {p l : ℕ} (E : Finset (Fin p × Fin l)) : Finset (Fin (p + l)) :=
  E.image fun e => Fin.castAdd l e.1

lemma endpoints_card {p l : ℕ} (E : Finset (Fin p × Fin l)) :
    (endpoints E).card = (E.image Prod.fst).card + (E.image Prod.snd).card := by
  have hc : Function.Injective (Fin.castAdd l : Fin p → Fin (p + l)) := by
    intro a b hab
    apply Fin.ext
    exact congrArg (fun x : Fin (p + l) => x.val) hab
  have hn : Function.Injective (Fin.natAdd p : Fin l → Fin (p + l)) := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    simp only [Fin.val_natAdd] at hv
    omega
  have hd : Disjoint (E.image fun e => Fin.castAdd l e.1)
      (E.image fun e => Fin.natAdd p e.2) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨⟨a, b⟩, _, hax⟩ := Finset.mem_image.mp hx
    obtain ⟨⟨a', b'⟩, _, hbx⟩ := Finset.mem_image.mp hy
    have hv := congrArg Fin.val (hax.trans hbx.symm)
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    have ha := a.isLt
    omega
  rw [endpoints, Finset.card_union_of_disjoint hd]
  have hl : E.image (fun e => Fin.castAdd l e.1) =
      (E.image Prod.fst).image (Fin.castAdd l) := by
    rw [Finset.image_image]
    rfl
  have hr : E.image (fun e => Fin.natAdd p e.2) =
      (E.image Prod.snd).image (Fin.natAdd p) := by
    rw [Finset.image_image]
    rfl
  rw [hl, hr, Finset.card_image_of_injective _ hc, Finset.card_image_of_injective _ hn]

lemma leftCover_card {p l : ℕ} (E : Finset (Fin p × Fin l)) :
    (leftCover E).card = (E.image Prod.fst).card := by
  have hc : Function.Injective (Fin.castAdd l : Fin p → Fin (p + l)) := by
    intro a b hab
    apply Fin.ext
    exact congrArg (fun x : Fin (p + l) => x.val) hab
  have he : leftCover E = (E.image Prod.fst).image (Fin.castAdd l) := by
    rw [Finset.image_image]
    rfl
  rw [he, Finset.card_image_of_injective _ hc]

lemma leftCover_covers {p l : ℕ} (E : Finset (Fin p × Fin l)) :
    ∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
      Fin.castAdd l a ∈ leftCover E ∨ Fin.natAdd p b ∈ leftCover E := by
  intro a b hab
  exact Or.inl (Finset.mem_image.mpr ⟨(a, b), hab, rfl⟩)

lemma residual_ledger {p l : ℕ} (E : Finset (Fin p × Fin l)) (v : Fin l)
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) :
    (residual E v).card + (leftCover (residual E v)).card =
      (endpoints (residual E v)).card := by
  rw [residual_card E v hfour, leftCover_card, endpoints_card]
  omega

lemma residual_subgraph_ledger {p l : ℕ}
    (E D : Finset (Fin p × Fin l)) (v : Fin l)
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (hD : D ⊆ residual E v) :
    D.card + (leftCover D).card = (endpoints D).card := by
  have hinj : Set.InjOn Prod.snd (D : Set (Fin p × Fin l)) := by
    intro x hx y hy hxy
    exact residual_right_injective E v hfour (hD hx) (hD hy) hxy
  have hc : (D.image Prod.snd).card = D.card := Finset.card_image_iff.mpr hinj
  rw [leftCover_card, endpoints_card, hc]
  omega

lemma residual_bound_of_endpoint_bound {p l : ℕ}
    (E : Finset (Fin p × Fin l)) (v : Fin l) (s : ℕ)
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (hsize : (endpoints (residual E v)).card ≤ s + 1) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ residual E v →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      (residual E v).card + S.card ≤ s + 1 := by
  refine ⟨leftCover (residual E v), leftCover_covers _, ?_⟩
  rw [residual_ledger E v hfour]
  exact hsize

lemma residual_subgraph_bound_of_endpoint_bound {p l : ℕ}
    (E D : Finset (Fin p × Fin l)) (v : Fin l) (s : ℕ)
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (hD : D ⊆ residual E v)
    (hsize : (endpoints D).card ≤ s + 1) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ D →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      D.card + S.card ≤ s + 1 := by
  refine ⟨leftCover D, leftCover_covers _, ?_⟩
  rw [residual_subgraph_ledger E D v hfour hD]
  exact hsize

end PEqualNP.Outside.L_meta_4970_aux.H5Deletion
