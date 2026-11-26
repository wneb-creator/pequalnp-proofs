import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux


namespace H5Pruning

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

end H5Pruning



namespace H5Compile

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

end H5Compile


namespace H5Reach

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

end H5Reach

namespace H5CompileReach
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

end H5CompileReach


namespace H5Bridge

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

end H5Bridge


namespace H5Bridge

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

end H5Bridge


namespace H5Deletion

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

end H5Deletion



namespace H5Count

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open H5Compile H5Pruning

def isAndOp : GateOp → Bool
  | .and => true
  | _ => false

def andCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => isAndOp g.op)

lemma andCount_nil : andCount [] = 0 := rfl

lemma andCount_cons (g : Gate) (gs : List Gate) :
    andCount (g :: gs) = andCount gs + if isAndOp g.op then 1 else 0 := by
  simp [andCount, List.countP_cons]

lemma andCount_append (gs hs : List Gate) :
    andCount (gs ++ hs) = andCount gs + andCount hs := by
  simp [andCount]

lemma emit_andCount (n : ℕ) (gs : List Gate) (op : GateOp) (a b : Option ℕ) :
    andCount (emit n gs op a b).1 ≤
      andCount gs + if isAndOp op then 1 else 0 := by
  cases a <;> cases b <;> cases op <;> simp [emit, andCount, isAndOp]

lemma step_andCount (n : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) :
    andCount (step n s g).1 ≤ andCount s.1 + if isAndOp g.op then 1 else 0 := by
  rcases g with ⟨op, ins⟩
  cases ins with
  | nil => simp [step]
  | cons a ins =>
      cases ins with
      | nil => simp [step]
      | cons b ins =>
          cases ins with
          | nil => simpa only [step] using
              emit_andCount n s.1 op (s.2.getD a none) (s.2.getD b none)
          | cons c ins => simp [step]

lemma fold_andCount (n : ℕ) (gs : List Gate) (s : List Gate × List (Option ℕ)) :
    andCount (gs.foldl (step n) s).1 ≤ andCount s.1 + andCount gs := by
  induction gs generalizing s with
  | nil => simp [andCount]
  | cons g gs ih =>
      have h := ih (step n s g)
      have hs := step_andCount n s g
      simp only [List.foldl_cons, andCount_cons]
      omega

lemma compile_andCount (n : ℕ) (gs : List Gate) :
    andCount (compile n gs).1 ≤ andCount gs := by
  simpa only [compile, initial, andCount_nil, Nat.zero_add] using
    fold_andCount n gs (initial n)

lemma zeroed_andCount_add_one (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = .and) :
    andCount (zeroed C j).gates + 1 = andCount C.gates := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have h := (List.take_append_drop j C.gates).symm
    rw [List.drop_eq_getElem_cons hj] at h
    exact h
  have hop' : (C.gates[j]).op = .and := by simpa [gateAt, hj] using hop
  conv_rhs => rw [hsplit]
  simp only [zeroed, andCount, List.countP_append, List.countP_cons, hop', isAndOp]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  omega

lemma compile_zeroed_andCount_lt (n : ℕ) (C : Circuit) (j : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = .and) :
    andCount (compile n (zeroed C j).gates).1 < andCount C.gates := by
  have hle := compile_andCount n (zeroed C j).gates
  have he := zeroed_andCount_add_one C j hj hop
  omega

lemma compiled_zeroed_andCount_lt (n : ℕ) (C D : Circuit) (j : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = .and)
    (hD : D.gates = (compile n (zeroed C j).gates).1) :
    andCount D.gates < andCount C.gates := by
  rw [hD]
  exact compile_zeroed_andCount_lt n C j hj hop

end H5Count

namespace H5LiftGlue

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970_aux.H5Pruning
open PEqualNP.Outside.L_meta_4970_aux.H5Reach

lemma wireFn_gate (n : ℕ) (C : Circuit) (hC : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool) :
    wireFn n C (n + j) x =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wireFn n C i x) := by
  unfold wireFn
  change (wiresFrom C.gates (List.ofFn x)).getD (n + j) false = _
  have he := getD_wiresFrom_gate C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at he
  rw [he, ← gateAt_get C j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp [hC j hj i hi, wiresFrom, Circuit.wires]

lemma orIn_singleton_true (n : ℕ) (C : Circuit) (hC : ReadsBack n C)
    (w : ℕ) (a : Fin n) (ha : a ∈ orIn n C w) :
    wireFn n C w (singletonInput a) = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwin : w < n
    · rw [orIn_input n C w hwin, Finset.mem_singleton] at ha
      subst a
      rw [wireFn_input n C w hwin]
      simp [singletonInput]
    · by_cases hwvalid : w < n + C.gates.length
      · let j := w - n
        have hj : j < C.gates.length := by omega
        have hwj : n + j = w := by omega
        rw [← hwj, orIn_gate n C hC j hj] at ha
        split_ifs at ha with hop
        · obtain ⟨u, hu, hau⟩ := Finset.mem_biUnion.mp ha
          have hu' := List.mem_toFinset.mp hu
          have hult := hC j hj u hu'
          have htrue := ih u (by omega) hau
          rw [← hwj, wireFn_gate n C hC j hj, hop]
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
          exact ⟨true, ⟨u, hu', htrue⟩, rfl⟩
        · exact (Finset.notMem_empty a ha).elim
      · rw [orIn_invalid n C w (by omega)] at ha
        exact (Finset.notMem_empty a ha).elim

lemma orIn_empty_of_false_singletons (n : ℕ) (C : Circuit) (hC : ReadsBack n C)
    (w : ℕ) (hz : ∀ a : Fin n, wireFn n C w (singletonInput a) = false) :
    orIn n C w = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro a ha
  have ht := orIn_singleton_true n C hC w a ha
  rw [hz a] at ht
  cases ht

lemma wire_false_singletons_of_below (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool)
    (hF : ∀ a : Fin n, F (singletonInput a) = false) (w : ℕ)
    (hBelow : ∀ x, wireFn n C w x = true → F x = true) :
    ∀ a : Fin n, wireFn n C w (singletonInput a) = false := by
  intro a
  cases hw : wireFn n C w (singletonInput a) with
  | false => rfl
  | true =>
      have h := hBelow (singletonInput a) hw
      rw [hF a] at h
      cases h

lemma safe_wire_orIn_empty (n : ℕ) (C : Circuit) (hC : ReadsBack n C)
    (F : (Fin n → Bool) → Bool) (hF : ∀ a : Fin n, F (singletonInput a) = false)
    (w : ℕ) (hBelow : ∀ x, wireFn n C w x = true → F x = true) :
    orIn n C w = ∅ :=
  orIn_empty_of_false_singletons n C hC w (wire_false_singletons_of_below n C F hF w hBelow)

lemma and_reader_implies (n : ℕ) (C : Circuit) (hC : ReadsBack n C)
    (g : ℕ) (hg : g < C.gates.length) (hop : (gateAt C g).op = .and)
    (i : ℕ) (hi : i ∈ (gateAt C g).inputs) (x : Fin n → Bool) :
    wireFn n C (n + g) x = true → wireFn n C i x = true := by
  intro h
  rw [wireFn_gate n C hC g hg, hop] at h
  simp only [GateOp.eval, List.all_eq_true, id_eq] at h
  exact h _ (List.mem_map.mpr ⟨i, hi, rfl⟩)

lemma zeroed_wire_prefix_eq (n : ℕ) (C : Circuit) (g : ℕ)
    (hg : g < C.gates.length) (w : ℕ) (hw : w < n + g) (x : Fin n → Bool) :
    wireFn n (zeroed C g) w x = wireFn n C w x := by
  unfold wireFn
  rw [zeroed_wires, wires_split C g hg]
  have hlen : (wiresFrom (C.gates.take g) (List.ofFn x)).length = n + g := by
    simp [length_wiresFrom, Nat.min_eq_left (Nat.le_of_lt hg)]
  rw [getD_wiresFrom_lt _ _ w (by simp [hlen]; omega),
    getD_wiresFrom_lt _ _ w (by simp [hlen]; omega)]
  rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]

lemma zero_and_reader_preserves_stars (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (F : (Fin n → Bool) → Bool) (hF : ∀ a : Fin n, F (singletonInput a) = false)
    (i g : ℕ) (hg : g < C.gates.length) (hop : (gateAt C g).op = .and)
    (hi : i ∈ (gateAt C g).inputs)
    (hBelow : ∀ x, wireFn n C i x = true → F x = true) :
    ∀ (Q : Finset (Fin n)) (w : ℕ),
      (∀ x, wireFn n C w x = starFun Q x) →
      ∀ x, wireFn n (zeroed C g) w x = starFun Q x := by
  intro Q w hstar
  apply zeroed_star_preserved_of_singletons n Q C hC g hg _ w hstar
  intro a ha
  apply wire_false_singletons_of_below n C F hF (n + g) _ a
  intro x hx
  exact hBelow x (and_reader_implies n C hC.2.1 g hg hop i hi x hx)

lemma zero_and_reader_output (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (F : (Fin n → Bool) → Bool) (hspec : ∀ x, wireFn n C C.output x = F x)
    (i g : ℕ) (hg : g < C.gates.length) (hop : (gateAt C g).op = .and)
    (hi : i ∈ (gateAt C g).inputs)
    (hBelow : ∀ x, wireFn n C i x = true → F x = true) :
    ∀ x, (wireFn n (zeroed C g) C.output x || wireFn n C i x) = F x := by
  intro x
  cases hix : wireFn n C i x with
  | false =>
      have hgx : wireFn n C (n + g) x = false := by
        cases hgx : wireFn n C (n + g) x with
        | false => rfl
        | true =>
            have h := and_reader_implies n C hC.2.1 g hg hop i hi x hgx
            rw [hix] at h
            cases h
      have heq := zeroed_eq_of_wire_false n C g hg x hgx
      simp only [Bool.or_false]
      unfold wireFn
      rw [heq]
      exact hspec x
  | true =>
      have hfx := hBelow x hix
      simp [hfx]

lemma zero_and_reader_output_internal (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (F : (Fin n → Bool) → Bool) (hspec : ∀ x, wireFn n C C.output x = F x)
    (i g : ℕ) (hg : g < C.gates.length) (hop : (gateAt C g).op = .and)
    (hi : i ∈ (gateAt C g).inputs)
    (hBelow : ∀ x, wireFn n C i x = true → F x = true) :
    ∀ x, (wireFn n (zeroed C g) C.output x || wireFn n (zeroed C g) i x) = F x := by
  intro x
  rw [zeroed_wire_prefix_eq n C g hg i (hC.2.1 g hg i hi)]
  exact zero_and_reader_output n C hC F hspec i g hg hop hi hBelow x

lemma graphFun_false_singletons {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : Fin n) : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (singletonInput a) = false := by
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
    false_and, exists_false, decide_false, Bool.false_or, decide_eq_false_iff_not]
  rintro ⟨u, v, huv, hu, hv⟩
  have hua : u = a := of_decide_eq_true hu
  have hva : v = a := of_decide_eq_true hv
  subst u
  subst v
  exact (G.ne_of_adj huv) rfl

end H5LiftGlue


namespace H5Lift

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.TwoColour
open H5Compile H5Pruning H5Bridge H5Reach H5CompileReach

def joinCircuit (n : ℕ) (gs : List Gate) (a : Option ℕ) (b : ℕ) : Circuit :=
  match a with
  | none => ⟨gs,b⟩
  | some a => ⟨gs ++ [⟨GateOp.or,[a,b]⟩], n + gs.length⟩

lemma join_good (n : ℕ) (gs : List Gate) (a : Option ℕ) (b : ℕ)
    (hg : good n gs) (ha : bounded n gs a) (hb : b < n + gs.length) :
    IsAO2 n (joinCircuit n gs a b) := by
  cases a with
  | none => exact hg
  | some a => exact good_append n gs .or a b hg (Or.inr rfl) (ha a rfl) hb

lemma join_size (n : ℕ) (gs : List Gate) (a : Option ℕ) (b : ℕ) :
    (joinCircuit n gs a b).size ≤ gs.length + 1 := by
  cases a <;> simp [joinCircuit, Circuit.size]

lemma join_value (n : ℕ) (gs : List Gate) (a : Option ℕ) (b : ℕ) (x : Fin n → Bool) :
    (joinCircuit n gs a b).eval (List.ofFn x) =
      (pointerValue (wireValues n gs x) a || (wireValues n gs x).getD b false) := by
  cases a with
  | none => simp [joinCircuit, Circuit.eval, Circuit.wires, wireValues, pointerValue]
  | some a =>
      change (wireValues n (gs ++ [⟨GateOp.or,[a,b]⟩]) x).getD (n+gs.length) false = _
      rw [wireValues_append, ← H5Compile.wireValues_length n gs x]
      simp [GateOp.eval, pointerValue]

lemma join_wire (n : ℕ) (gs : List Gate) (a : Option ℕ) (b w : ℕ)
    (hw : w < n + gs.length) (x : Fin n → Bool) :
    wireFn n (joinCircuit n gs a b) w x = (wireValues n gs x).getD w false := by
  cases a with
  | none => rfl
  | some a =>
      change (wireValues n (gs ++ [⟨GateOp.or,[a,b]⟩]) x).getD w false = _
      rw [wireValues_append]
      exact List.getD_append _ _ _ _ (by rw [H5Compile.wireValues_length]; exact hw)

lemma zeroed_prefix (n : ℕ) (C : Circuit) (g w : ℕ) (hg : g < C.gates.length)
    (hw : w < n+g) (x : Fin n → Bool) :
    wireFn n (zeroed C g) w x = wireFn n C w x := by
  unfold wireFn
  rw [zeroed_wires, wires_split C g hg]
  have hp : w < (wiresFrom (C.gates.take g) (List.ofFn x)).length := by
    rw [length_wiresFrom]
    simp only [List.length_ofFn, List.length_take]
    rw [Nat.min_eq_left (by omega)]
    exact hw
  rw [getD_wiresFrom_lt _ _ _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
    getD_wiresFrom_lt _ _ _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
    List.getD_append _ _ _ _ hp, List.getD_append _ _ _ _ hp]

lemma join_tCount (n : ℕ) (gs : List Gate) (a : Option ℕ) (b : ℕ)
    (hg : good n gs) (ha : bounded n gs a) (hb : b < n + gs.length)
    (lin : ℕ → Bool) (hT : tCount n ⟨gs,0⟩ lin = 0)
    (har : pointerReach (reachValues n gs) a = ∅)
    (hbr : (reachValues n gs).getD b ∅ = ∅) :
    tCount n (joinCircuit n gs a b) lin = 0 := by
  classical
  have hmono := (tCount_zero_iff_reachValues n ⟨gs,0⟩ lin hg.2.1).mp hT
  apply (tCount_zero_iff_reachValues n (joinCircuit n gs a b) lin (join_good n gs a b hg ha hb).2.1).mpr
  cases a with
  | none => exact hmono
  | some a =>
      have hreach : reachValues n (joinCircuit n gs (some a) b).gates = reachValues n gs ++ [∅] := by
        change reachValues n (gs ++ [⟨GateOp.or,[a,b]⟩]) = _
        rw [H5CompileReach.reachValues_append]
        simp only [pointerReach] at har
        simp only [gateReach, List.toFinset_cons, List.toFinset_nil,
          Finset.biUnion_insert, Finset.biUnion_empty, har, hbr, Finset.empty_union, ite_self]
      intro w u hu v hv
      rw [hreach] at hu hv
      by_cases hw : w < (reachValues n gs).length
      · rw [List.getD_append _ _ _ _ hw] at hu hv
        exact hmono w u hu v hv
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hu
        have hempty : ([∅] : List (Finset (Fin n))).getD (w - (reachValues n gs).length) ∅ = ∅ := by
          cases w - (reachValues n gs).length <;> simp
        rw [hempty] at hu
        simp at hu

end H5Lift


namespace H5Lift

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.TwoColour
open H5Compile H5Pruning H5Bridge H5Reach H5CompileReach H5Count H5LiftGlue

lemma join_andCount (n : ℕ) (gs : List Gate) (a : Option ℕ) (b : ℕ) :
    andCount (joinCircuit n gs a b).gates = andCount gs := by
  cases a <;> simp [joinCircuit, andCount, isAndOp]

lemma and_reader_lift (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (F : (Fin n → Bool) → Bool) (hsingle : ∀ a : Fin n, F (singletonInput a) = false)
    (hspec : ∀ x, wireFn n C C.output x = F x)
    (i g : ℕ) (hg : g < C.gates.length) (hop : (gateAt C g).op = .and)
    (himem : i ∈ (gateAt C g).inputs)
    (hBelow : ∀ x, wireFn n C i x = true → F x = true)
    (hpos : ∃ x, wireFn n C i x = true)
    (lin : ℕ → Bool) (hT : tCount n C lin = 0) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ andCount D.gates < andCount C.gates ∧
      (∀ x, wireFn n D D.output x = F x) ∧ tCount n D lin = 0 ∧
      ∀ (Q : Finset (Fin n)) (w : ℕ), 2 ≤ Q.card →
        (∀ x, wireFn n C w x = starFun Q x) →
        ∃ k < D.gates.length, (gateAt D k).op = .or ∧
          ∀ x, wireFn n D (n+k) x = starFun Q x := by
  classical
  let C0 := zeroed C g
  let code := (compile n C0.gates).1
  let rs := (compile n C0.gates).2
  let a := rs.getD C.output none
  have hallowed : ∀ q ∈ C0.gates, allowed q := zeroed_allowed n C hC g
  have hgood : good n code := compile_good n C0.gates hallowed
  have hptr : validPointers n code rs := fold_bounds n C0.gates (initial n) (initial_bounds n)
  have hback : ReadsBack n C0 := zeroed_readsBack n C g hg hC.2.1
  have hi : i < n+g := hC.2.1 g hg i himem
  have hib : ∃ b, rs.getD i none = some b := by
    cases hb : rs.getD i none with
    | some b => exact ⟨b,rfl⟩
    | none =>
        obtain ⟨x,hx⟩ := hpos
        have h := compile_value n C0.gates hallowed i x
        change pointerValue (wireValues n code x) (rs.getD i none) = wireFn n C0 i x at h
        rw [hb] at h
        change false = wireFn n (zeroed C g) i x at h
        rw [zeroed_prefix n C g i hg hi x, hx] at h
        contradiction
  obtain ⟨b,hb⟩ := hib
  have hbb : b < n+code.length := get_pointer_bound n code rs hptr i b hb
  have hab : bounded n code a := get_pointer_bound n code rs hptr C.output
  let D := joinCircuit n code a b
  have hAO : IsAO2 n D := join_good n code a b hgood hab hbb
  have hO : ∀ x, pointerValue (wireValues n code x) a = wireFn n C0 C.output x := by
    intro x
    exact compile_value n C0.gates hallowed C.output x
  have hI : ∀ x, (wireValues n code x).getD b false = wireFn n C0 i x := by
    intro x
    have h := compile_value n C0.gates hallowed i x
    change pointerValue (wireValues n code x) (rs.getD i none) = wireFn n C0 i x at h
    rw [hb] at h
    exact h
  have hfun : ∀ x, wireFn n D D.output x = F x := by
    intro x
    change (joinCircuit n code a b).eval (List.ofFn x) = F x
    rw [join_value, hO, hI]
    exact zero_and_reader_output_internal n C hC F hspec i g hg hop himem hBelow x
  have hsize : D.size ≤ C.size := by
    have hc := compile_size n C0.gates
    have hj := join_size n code a b
    have hz := zeroed_binaryCount_lt C g hg
    change (compile n (zeroed C g).gates).1.length ≤ binaryCount (zeroed C g).gates at hc
    change D.size ≤ (compile n (zeroed C g).gates).1.length + 1 at hj
    omega
  have hcount : andCount D.gates < andCount C.gates := by
    rw [show D = joinCircuit n code a b from rfl, join_andCount]
    exact compile_zeroed_andCount_lt n C g hg hop
  have hbelow0 : ∀ w, (∀ x, wireFn n C w x = true → F x = true) →
      ∀ x, wireFn n C0 w x = true → F x = true := by
    intro w hw x hx
    exact hw x ((Bool.le_iff_imp.mp (zeroed_wire_le n C hC g hg w x)) hx)
  have hor : orIn n C0 C.output = ∅ := safe_wire_orIn_empty n C0 hback F hsingle C.output
    (hbelow0 C.output (fun x hx => (hspec x).symm.trans hx))
  have hir : orIn n C0 i = ∅ := safe_wire_orIn_empty n C0 hback F hsingle i (hbelow0 i hBelow)
  have har : pointerReach (reachValues n code) a = ∅ := by
    have h := compile_reach n C0.gates hallowed C.output
    rw [reachValues_eq_orIn n C0 hback, hor] at h
    exact h
  have hbr : (reachValues n code).getD b ∅ = ∅ := by
    have h := compile_reach n C0.gates hallowed i
    change pointerReach (reachValues n code) (rs.getD i none) = _ at h
    rw [hb] at h
    rw [reachValues_eq_orIn n C0 hback, hir] at h
    exact h
  have hT0 : tCount n C0 lin = 0 := zeroed_tCount n C g hg hC.2.1 lin hT
  have hTc : tCount n ⟨code,0⟩ lin = 0 := compile_tCount_zero n C0 lin hallowed hback hT0 0
  have hTD : tCount n D lin = 0 := join_tCount n code a b hgood hab hbb lin hTc har hbr
  refine ⟨D,hAO,hsize,hcount,hfun,hTD,?_⟩
  intro Q w hQ hstar
  have hz := zero_and_reader_preserves_stars n C hC F hsingle i g hg hop himem hBelow Q w hstar
  obtain ⟨k,hk,_,hval⟩ := compiled_star n C0 ⟨code,0⟩ hallowed rfl hgood Q hQ w hz
  change k < code.length at hk
  apply pure_star_or_root n D hAO Q hQ (n+k)
  intro x
  rw [show D = joinCircuit n code a b from rfl, join_wire n code a b (n+k) (by omega)]
  exact hval x

end H5Lift

namespace H5AndTotal

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.TwoColour
open H5Compile H5Pruning H5Bridge H5Reach H5CompileReach H5Count H5LiftGlue H5Lift

def compiledCircuit (n : ℕ) (C : Circuit) : Circuit :=
  let code := (compile n C.gates).1
  let output := (compile n C.gates).2.getD C.output none
  ⟨code, output.getD (n + code.length)⟩

lemma compiledCircuit_good (n : ℕ) (C : Circuit)
    (hgs : ∀ g ∈ C.gates, allowed g) : IsAO2 n (compiledCircuit n C) :=
  compile_good n C.gates hgs

lemma compiledCircuit_size (n : ℕ) (C : Circuit) :
    (compiledCircuit n C).size ≤ binaryCount C.gates :=
  compile_size n C.gates

lemma compiledCircuit_value (n : ℕ) (C : Circuit)
    (hgs : ∀ g ∈ C.gates, allowed g) (x : Fin n → Bool) :
    wireFn n (compiledCircuit n C) (compiledCircuit n C).output x =
      wireFn n C C.output x := by
  have h := compile_value n C.gates hgs C.output x
  cases ho : (compile n C.gates).2.getD C.output none with
  | none =>
      rw [ho] at h
      change false = wireFn n C C.output x at h
      rw [← h]
      change (wireValues n (compile n C.gates).1 x).getD
        (Option.getD ((compile n C.gates).2.getD C.output none)
          (n + (compile n C.gates).1.length)) false = false
      rw [ho]
      apply List.getD_eq_default
      rw [H5Compile.wireValues_length]
      simp
  | some o =>
      rw [ho] at h
      change (wireValues n (compile n C.gates).1 x).getD
        (Option.getD ((compile n C.gates).2.getD C.output none)
          (n + (compile n C.gates).1.length)) false = _
      rw [ho]
      exact h

lemma compiled_circuit_total (n : ℕ) (C : Circuit)
    (hgs : ∀ g ∈ C.gates, allowed g) :
    ∃ D : Circuit, IsAO2 n D ∧ D.gates = (compile n C.gates).1 ∧
      D.size ≤ binaryCount C.gates ∧
      ∀ x, wireFn n D D.output x = wireFn n C C.output x := by
  exact ⟨compiledCircuit n C, compiledCircuit_good n C hgs, rfl,
    compiledCircuit_size n C, compiledCircuit_value n C hgs⟩

lemma and_reader_lift_total (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (F : (Fin n → Bool) → Bool) (hsingle : ∀ a : Fin n, F (singletonInput a) = false)
    (hspec : ∀ x, wireFn n C C.output x = F x)
    (i g : ℕ) (hg : g < C.gates.length) (hop : (gateAt C g).op = .and)
    (himem : i ∈ (gateAt C g).inputs)
    (hBelow : ∀ x, wireFn n C i x = true → F x = true)
    (lin : ℕ → Bool) (hT : tCount n C lin = 0) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ andCount D.gates < andCount C.gates ∧
      (∀ x, wireFn n D D.output x = F x) ∧ tCount n D lin = 0 ∧
      ∀ (Q : Finset (Fin n)) (w : ℕ), 2 ≤ Q.card →
        (∀ x, wireFn n C w x = starFun Q x) →
        ∃ k < D.gates.length, (gateAt D k).op = .or ∧
          ∀ x, wireFn n D (n+k) x = starFun Q x := by
  classical
  by_cases hpos : ∃ x, wireFn n C i x = true
  · exact and_reader_lift n C hC F hsingle hspec i g hg hop himem hBelow hpos lin hT
  · have hfalse : ∀ x, wireFn n C i x = false := by
      intro x
      cases hi : wireFn n C i x with
      | false => rfl
      | true => exact (hpos ⟨x, hi⟩).elim
    let C0 := zeroed C g
    let D := compiledCircuit n C0
    have hallowed : ∀ q ∈ C0.gates, allowed q := zeroed_allowed n C hC g
    have hAO : IsAO2 n D := compiledCircuit_good n C0 hallowed
    have hsize : D.size ≤ C.size := by
      have hc := compiledCircuit_size n C0
      have hz := zeroed_binaryCount_lt C g hg
      change D.size ≤ binaryCount (zeroed C g).gates at hc
      omega
    have hcount : andCount D.gates < andCount C.gates :=
      compile_zeroed_andCount_lt n C g hg hop
    have hfun0 : ∀ x, wireFn n C0 C0.output x = F x := by
      intro x
      have h := zero_and_reader_output n C hC F hspec i g hg hop himem hBelow x
      change wireFn n (zeroed C g) C.output x = F x
      simpa only [hfalse x, Bool.or_false] using h
    have hfun : ∀ x, wireFn n D D.output x = F x := by
      intro x
      rw [show D = compiledCircuit n C0 from rfl, compiledCircuit_value n C0 hallowed]
      exact hfun0 x
    have hback : ReadsBack n C0 := zeroed_readsBack n C g hg hC.2.1
    have hT0 : tCount n C0 lin = 0 := zeroed_tCount n C g hg hC.2.1 lin hT
    have hTD : tCount n D lin = 0 :=
      compiled_tCount_zero n C0 D lin hallowed hback hT0 rfl
    refine ⟨D, hAO, hsize, hcount, hfun, hTD, ?_⟩
    intro Q w hQ hstar
    have hz := zero_and_reader_preserves_stars n C hC F hsingle i g hg hop himem hBelow Q w hstar
    exact compiled_star n C0 D hallowed rfl hAO Q hQ w hz

end H5AndTotal

namespace H5OrLift

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def isAndOp : GateOp → Bool
  | GateOp.and => true
  | _ => false

lemma isAndOp_eq_true_iff (op : GateOp) : isAndOp op = true ↔ op = GateOp.and := by
  cases op <;> simp [isAndOp]

def andCount (C : Circuit) : ℕ :=
  ((Finset.range C.gates.length).filter fun k => isAndOp (gateAt C k).op = true).card

def andIndexSum (C : Circuit) : ℕ :=
  ∑ k ∈ (Finset.range C.gates.length).filter (fun k => isAndOp (gateAt C k).op = true), k

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

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  exact foldl_wireStep_length C.gates x

lemma gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

lemma wireVal_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wireVal n C w x = x ⟨w, hw⟩ := by
  unfold wireVal Circuit.wires
  have hw' : w < (List.ofFn x).length := by simp [hw]
  have h1 := foldl_wireStep_prefix C.gates (List.ofFn x) w hw'
  change (C.gates.foldl wireStep (List.ofFn x)).getD w false = x ⟨w, hw⟩
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw']
  simp

lemma wireVal_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length) (hRB : ReadsBack n C) :
    wireVal n C (n + k) x =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun u => wireVal n C u x) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take k).foldl wireStep (List.ofFn x) with hacc
  have hacc_len : acc.length = n + k := by
    rw [hacc, foldl_wireStep_length, List.length_ofFn, List.length_take]
    omega
  have hpref : ∀ u < n + k, wireVal n C u x = acc.getD u false := by
    intro u hu
    unfold wireVal Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD u false = acc.getD u false
    conv_lhs => rw [← List.take_append_drop k C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_wireStep_prefix (C.gates.drop k) acc u (by omega)
  have hval : wireVal n C (n + k) x =
      C.gates[k].op.eval (C.gates[k].inputs.map fun u => acc.getD u false) := by
    unfold wireVal Circuit.wires
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

lemma wireVal_append_lt (n : ℕ) (C : Circuit) (g : Gate) (out : ℕ) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n + C.gates.length) :
    wireVal n ⟨C.gates ++ [g], out⟩ w x = wireVal n C w x := by
  unfold wireVal Circuit.wires
  change ((C.gates ++ [g]).foldl wireStep (List.ofFn x)).getD w false =
    (C.gates.foldl wireStep (List.ofFn x)).getD w false
  rw [List.foldl_append]
  have hw' : w < (C.gates.foldl wireStep (List.ofFn x)).length := by
    rw [foldl_wireStep_length, List.length_ofFn]
    exact hw
  exact foldl_wireStep_prefix [g] (C.gates.foldl wireStep (List.ofFn x)) w hw'

lemma wireVal_append_last (n : ℕ) (C : Circuit) (g : Gate) (out : ℕ) (x : Fin n → Bool) :
    wireVal n ⟨C.gates ++ [g], out⟩ (n + C.gates.length) x =
      g.op.eval (g.inputs.map fun u => wireVal n C u x) := by
  unfold wireVal Circuit.wires
  change ((C.gates ++ [g]).foldl wireStep (List.ofFn x)).getD (n + C.gates.length) false = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  set acc := C.gates.foldl wireStep (List.ofFn x) with hacc
  have hlen : acc.length = n + C.gates.length := by
    rw [hacc, foldl_wireStep_length, List.length_ofFn]
  rw [List.getD_eq_getElem?_getD]
  simp only [wireStep, List.getElem?_append_right (by omega : acc.length ≤ n + C.gates.length),
    hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rfl

lemma output_lt_of_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hE : G.edgeFinset.Nonempty) (hF : circuitFun n C = graphFun G ∅) :
    C.output < n + C.gates.length := by
  by_contra hge
  push Not at hge
  obtain ⟨e, he⟩ := hE
  induction e using Sym2.ind with
  | _ u v =>
    have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
    have htrue : graphFun G ∅ (fun _ => true) = true := by
      unfold graphFun
      rw [Bool.or_eq_true]
      right
      rw [decide_eq_true_eq]
      exact ⟨u, v, hadj, rfl, rfl⟩
    have hfalse : circuitFun n C (fun _ => true) = false := by
      unfold circuitFun Circuit.eval
      rw [List.getD_eq_getElem?_getD]
      have hlen : (C.wires (List.ofFn (fun _ : Fin n => true))).length = n + C.gates.length := by
        rw [wires_length, List.length_ofFn]
      rw [List.getElem?_eq_none (by omega)]
      rfl
    have hEq := congrFun hF (fun _ => true)
    rw [hfalse, htrue] at hEq
    cases hEq

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
      gateAt_eq_getElem C j hj]
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

lemma exists_direct_reader (n : ℕ) (C : Circuit) (i j : ℕ)
    (hj : j < C.gates.length) (h : InCone n C i j) :
    ∃ g, i < g ∧ g ≤ j ∧ g < C.gates.length ∧ n + i ∈ (gateAt C g).inputs := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [inCone_iff n C i j hj] at h
    obtain ⟨w, hw, hnw, hlt, hcase⟩ := h
    rcases hcase with rfl | hcone
    · refine ⟨j, by omega, le_refl j, hj, ?_⟩
      have heq : n + (w - n) = w := by omega
      rw [heq]
      exact hw
    · have hklt : w - n < j := by omega
      obtain ⟨g, hig, hgk, hglen, hmem⟩ := ih (w - n) hklt (by omega) hcone
      exact ⟨g, hig, by omega, hglen, hmem⟩

def remap (n g r w : ℕ) : ℕ :=
  if w < n + g then w
  else if w = n + g then r
  else w - 1

def origWire (n g w : ℕ) : ℕ :=
  if w < n + g then w else w + 1

def mapGate (f : ℕ → ℕ) (gt : Gate) : Gate :=
  ⟨gt.op, gt.inputs.map f⟩

def delGate (n g r : ℕ) (C : Circuit) : Circuit :=
  ⟨(C.gates.eraseIdx g).map (mapGate (remap n g r)), remap n g r C.output⟩

lemma delGate_length (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length) :
    (delGate n g r C).gates.length = C.gates.length - 1 := by
  simp [delGate, List.length_eraseIdx_of_lt hg]

lemma delGate_gateAt (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length)
    (k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (delGate n g r C) k =
      mapGate (remap n g r) (gateAt C (if k < g then k else k + 1)) := by
  have hk' : k < (delGate n g r C).gates.length := by
    rw [delGate_length n g r C hg]; exact hk
  rw [gateAt_eq_getElem (delGate n g r C) k hk']
  have hk_e : k < (C.gates.eraseIdx g).length := by
    rw [List.length_eraseIdx_of_lt hg]; exact hk
  simp only [delGate, List.getElem_map]
  split_ifs with hkg
  · rw [List.getElem_eraseIdx_of_lt hk_e hkg, gateAt_eq_getElem C k (by omega)]
  · rw [List.getElem_eraseIdx_of_ge hk_e (by omega), gateAt_eq_getElem C (k + 1) (by omega)]

lemma delGate_isAO2 (n g r : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hg : g < C.gates.length) (hr : r < n + g) :
    IsAO2 n (delGate n g r C) := by
  rcases hAO with ⟨hAOOnly, hRB, hLen2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro gt hgt
    simp only [delGate, List.mem_map] at hgt
    obtain ⟨gt0, hgt0, rfl⟩ := hgt
    exact hAOOnly gt0 (List.mem_of_mem_eraseIdx hgt0)
  · intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap
      split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap
      split_ifs <;> omega
  · intro gt hgt
    simp only [delGate, List.mem_map] at hgt
    obtain ⟨gt0, hgt0, rfl⟩ := hgt
    simp only [mapGate, List.length_map]
    exact hLen2 gt0 (List.mem_of_mem_eraseIdx hgt0)

lemma delGate_output_lt (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length)
    (hr : r < n + g) (hout : C.output < n + C.gates.length) :
    (delGate n g r C).output < n + (delGate n g r C).gates.length := by
  rw [delGate_length n g r C hg]
  simp only [delGate, remap]
  split_ifs <;> omega

lemma origWire_remap_ne (n g r u : ℕ) (hne : u ≠ n + g) :
    origWire n g (remap n g r u) = u := by
  unfold origWire remap
  split_ifs <;> omega

lemma origWire_remap_eq (n g r : ℕ) (hr : r < n + g) :
    origWire n g (remap n g r (n + g)) = r := by
  unfold origWire remap
  split_ifs <;> omega

lemma delGate_wireVal_eq (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g)
    (hmatch : wireVal n C (n + g) x = wireVal n C r x) :
    ∀ w < n + (delGate n g r C).gates.length,
      wireVal n (delGate n g r C) w x = wireVal n C (origWire n g w) x := by
  have hAO_rb : ReadsBack n (delGate n g r C) := by
    intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap; split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap; split_ifs <;> omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wireVal_input n (delGate n g r C) x w hwn]
      have horig : origWire n g w = w := by unfold origWire; split_ifs <;> omega
      rw [horig, wireVal_input n C x w hwn]
    · set k := w - n with hk_def
      have hw_eq : w = n + k := by omega
      have hk_lt : k < (delGate n g r C).gates.length := by omega
      have hk_lt' : k < C.gates.length - 1 := by
        rw [← delGate_length n g r C hg]; exact hk_lt
      rw [hw_eq, wireVal_gate n (delGate n g r C) x k hk_lt hAO_rb]
      rw [delGate_gateAt n g r C hg k hk_lt']
      set k0 := if k < g then k else k + 1 with hk0_def
      have hk0_lt : k0 < C.gates.length := by
        rw [hk0_def]; split_ifs <;> omega
      have horig : origWire n g (n + k) = n + k0 := by
        unfold origWire; rw [hk0_def]; split_ifs <;> omega
      rw [horig, wireVal_gate n C x k0 hk0_lt hRB]
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hru_lt : remap n g r u < n + k := by
        have h1 : remap n g r u ∈ (gateAt (delGate n g r C) k).inputs := by
          rw [delGate_gateAt n g r C hg k hk_lt']
          simp only [mapGate, List.mem_map]
          exact ⟨u, hu, rfl⟩
        exact hAO_rb k hk_lt (remap n g r u) h1
      have hih := ih (remap n g r u) (by omega) (by omega)
      simp only [Function.comp_apply, hih]
      by_cases hug : u = n + g
      · rw [hug, origWire_remap_eq n g r hr, hmatch]
      · rw [origWire_remap_ne n g r u hug]

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l1 l2 : List Bool) (hlen : l1.length = l2.length)
    (hmono : ∀ p (hp1 : p < l1.length) (hp2 : p < l2.length), l1[p] = true → l2[p] = true) :
    op.eval l1 = true → op.eval l2 = true := by
  rcases hop with rfl | rfl
  · intro h1
    simp only [GateOp.eval, List.all_eq_true, id_eq] at h1 ⊢
    intro b hb
    rw [List.mem_iff_getElem] at hb
    obtain ⟨p, hp2, rfl⟩ := hb
    have hp1 : p < l1.length := by omega
    exact hmono p hp1 hp2 (h1 l1[p] (List.getElem_mem hp1))
  · intro h1
    simp only [GateOp.eval, List.any_eq_true, id_eq] at h1 ⊢
    obtain ⟨b, hb, rfl⟩ := h1
    rw [List.mem_iff_getElem] at hb
    obtain ⟨p, hp1, hbp⟩ := hb
    have hp2 : p < l2.length := by omega
    exact ⟨l2[p], List.getElem_mem hp2, hmono p hp1 hp2 hbp⟩

lemma delGate_wireVal_mono (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hAOOnly : AndOrOnly C) (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g)
    (hmono_g : wireVal n C (n + g) x = true → wireVal n C r x = true) :
    ∀ w < n + (delGate n g r C).gates.length,
      wireVal n C (origWire n g w) x = true → wireVal n (delGate n g r C) w x = true := by
  have hAO_rb : ReadsBack n (delGate n g r C) := by
    intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap; split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap; split_ifs <;> omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw htrue
    by_cases hwn : w < n
    · rw [wireVal_input n (delGate n g r C) x w hwn]
      have horig : origWire n g w = w := by unfold origWire; split_ifs <;> omega
      rw [horig, wireVal_input n C x w hwn] at htrue
      exact htrue
    · set k := w - n with hk_def
      have hw_eq : w = n + k := by omega
      have hk_lt : k < (delGate n g r C).gates.length := by omega
      have hk_lt' : k < C.gates.length - 1 := by
        rw [← delGate_length n g r C hg]; exact hk_lt
      rw [hw_eq] at htrue ⊢
      rw [wireVal_gate n (delGate n g r C) x k hk_lt hAO_rb]
      rw [delGate_gateAt n g r C hg k hk_lt']
      set k0 := if k < g then k else k + 1 with hk0_def
      have hk0_lt : k0 < C.gates.length := by
        rw [hk0_def]; split_ifs <;> omega
      have horig : origWire n g (n + k) = n + k0 := by
        unfold origWire; rw [hk0_def]; split_ifs <;> omega
      rw [horig, wireVal_gate n C x k0 hk0_lt hRB] at htrue
      simp only [mapGate, List.map_map]
      have hop : (gateAt C k0).op = GateOp.and ∨ (gateAt C k0).op = GateOp.or := by
        rw [gateAt_eq_getElem C k0 hk0_lt]
        exact hAOOnly C.gates[k0] (List.getElem_mem hk0_lt)
      apply gateOp_eval_mono (gateAt C k0).op hop _ _ (by simp) _ htrue
      intro p hp1 hp2 hv
      simp only [List.getElem_map, Function.comp_apply] at hv ⊢
      set u := (gateAt C k0).inputs[p]'(by simpa using hp1) with hu_def
      have hu_mem : u ∈ (gateAt C k0).inputs := List.getElem_mem (by simpa using hp1)
      have hru_lt : remap n g r u < n + k := by
        have h1 : remap n g r u ∈ (gateAt (delGate n g r C) k).inputs := by
          rw [delGate_gateAt n g r C hg k hk_lt']
          simp only [mapGate, List.mem_map]
          exact ⟨u, hu_mem, rfl⟩
        exact hAO_rb k hk_lt (remap n g r u) h1
      apply ih (remap n g r u) (by omega) (by omega)
      by_cases hug : u = n + g
      · rw [hug, origWire_remap_eq n g r hr]
        rw [hug] at hv
        exact hmono_g hv
      · rw [origWire_remap_ne n g r u hug]
        exact hv

lemma delGate_wireVal_prefix_eq (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g) :
    ∀ w < n + g, wireVal n (delGate n g r C) w x = wireVal n C w x := by
  have hAO_rb : ReadsBack n (delGate n g r C) := by
    intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap; split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap; split_ifs <;> omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wireVal_input n (delGate n g r C) x w hwn, wireVal_input n C x w hwn]
    · set k := w - n with hk_def
      have hw_eq : w = n + k := by omega
      have hkg : k < g := by omega
      have hk_lt : k < (delGate n g r C).gates.length := by
        rw [delGate_length n g r C hg]; omega
      rw [hw_eq, wireVal_gate n (delGate n g r C) x k hk_lt hAO_rb]
      rw [delGate_gateAt n g r C hg k (by omega)]
      simp only [hkg, ↓reduceIte]
      rw [wireVal_gate n C x k (by omega) hRB]
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hu_lt : u < n + k := hRB k (by omega) u hu
      have hrm : remap n g r u = u := by unfold remap; split_ifs <;> omega
      simp only [Function.comp_apply, hrm]
      exact ih u (by omega) (by omega)

def pushOr (n g y i : ℕ) (C : Circuit) : Circuit :=
  let Cmid := delGate n g y C
  ⟨Cmid.gates ++ [⟨GateOp.or, [Cmid.output, n + i]⟩], n + Cmid.gates.length⟩

def shiftDown (g k : ℕ) : ℕ :=
  if k < g then k else k - 1

lemma pushOr_step (n : ℕ) (F : (Fin n → Bool) → Bool)
    (C : Circuit) (i g j : ℕ)
    (hAO : IsAO2 n C) (hF : circuitFun n C = F)
    (hout : C.output < n + C.gates.length)
    (hig : i < g) (hgj : g < j) (hj : j < C.gates.length)
    (hBelow : ∀ x : Fin n → Bool, wireVal n C (n+i) x = true → F x = true)
    (hgOr : (gateAt C g).op = GateOp.or)
    (hjAnd : (gateAt C j).op = GateOp.and)
    (hmem : n + i ∈ (gateAt C g).inputs) :
    ∃ y < n+g, ((gateAt C g).inputs = [n+i,y] ∨ (gateAt C g).inputs = [y,n+i]) ∧
      IsAO2 n (pushOr n g y i C) ∧ circuitFun n (pushOr n g y i C) = F ∧
      (pushOr n g y i C).size = C.size ∧
      andCount (pushOr n g y i C) = andCount C ∧
      andIndexSum (pushOr n g y i C) < andIndexSum C := by
  rcases hAO with ⟨hAOOnly, hRB, hLen2⟩
  have hg : g < C.gates.length := by omega
  have hgin_len : (gateAt C g).inputs.length = 2 := by
    rw [gateAt_eq_getElem C g hg]
    exact hLen2 C.gates[g] (List.getElem_mem hg)
  rcases hgin : (gateAt C g).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · simp [hgin] at hgin_len
  · simp [hgin] at hgin_len
  · have hmem' : n + i = a ∨ n + i = b := by
      simpa [hgin] using hmem
    set y := if a = n + i then b else a with hy_def
    have hy_mem : y ∈ (gateAt C g).inputs := by
      rw [hgin, hy_def]
      split_ifs <;> simp
    have hy_lt : y < n + g := hRB g hg y hy_mem
    have hg_eval : ∀ x : Fin n → Bool,
        wireVal n C (n + g) x = (wireVal n C (n + i) x || wireVal n C y x) := by
      intro x
      rw [wireVal_gate n C x g hg hRB, hgOr, hgin]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false]
      rw [hy_def]
      split_ifs with ha
      · rw [ha]
      · rcases hmem' with rfl | rfl
        · exact absurd rfl ha
        · exact Bool.or_comm _ _
    set Cmid := delGate n g y C with hCmid
    set C' := pushOr n g y i C with hC'
    have hCmid_len : Cmid.gates.length = C.gates.length - 1 := delGate_length n g y C hg
    have hC'_len : C'.gates.length = C.gates.length := by
      simp only [hC', pushOr, List.length_append, List.length_singleton, ← hCmid, hCmid_len]
      omega
    have hCmid_AO : IsAO2 n Cmid := delGate_isAO2 n g y C ⟨hAOOnly, hRB, hLen2⟩ hg hy_lt
    have hCmid_out : Cmid.output < n + Cmid.gates.length :=
      delGate_output_lt n g y C hg hy_lt hout
    have hC'_AO : IsAO2 n C' := by
      rcases hCmid_AO with ⟨h1, h2, h3⟩
      refine ⟨?_, ?_, ?_⟩
      · intro gt hgt
        simp only [hC', pushOr, ← hCmid, List.mem_append, List.mem_singleton] at hgt
        rcases hgt with hgt | rfl
        · exact h1 gt hgt
        · exact Or.inr rfl
      · intro k hk w hw
        have hk' : k < Cmid.gates.length + 1 := by
          simpa [hC', pushOr, ← hCmid] using hk
        by_cases hkm : k < Cmid.gates.length
        · have hgat : gateAt C' k = gateAt Cmid k := by
            rw [gateAt_eq_getElem C' k hk, gateAt_eq_getElem Cmid k hkm]
            simp [hC', pushOr, ← hCmid, List.getElem_append_left hkm]
          rw [hgat] at hw
          exact h2 k hkm w hw
        · have hkeq : k = Cmid.gates.length := by omega
          have hgat : gateAt C' k = ⟨GateOp.or, [Cmid.output, n + i]⟩ := by
            rw [gateAt_eq_getElem C' k hk]
            simp [hC', pushOr, ← hCmid, hkeq]
          rw [hgat] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · omega
          · rw [hkeq, hCmid_len]; omega
      · intro gt hgt
        simp only [hC', pushOr, ← hCmid, List.mem_append, List.mem_singleton] at hgt
        rcases hgt with hgt | rfl
        · exact h3 gt hgt
        · rfl
    have hC'_F : circuitFun n C' = F := by
      funext x
      have hlast : circuitFun n C' x =
          (wireVal n Cmid Cmid.output x || wireVal n Cmid (n + i) x) := by
        change wireVal n C' (n + Cmid.gates.length) x = _
        have h := wireVal_append_last n Cmid ⟨GateOp.or, [Cmid.output, n + i]⟩
          (n + Cmid.gates.length) x
        simpa [hC', pushOr, ← hCmid, GateOp.eval] using h
      rw [hlast]
      have hni : wireVal n Cmid (n + i) x = wireVal n C (n + i) x :=
        delGate_wireVal_prefix_eq n g y C x hRB hg hy_lt (n + i) (by omega)
      rw [hni]
      cases hvi : wireVal n C (n + i) x
      · have hmatch : wireVal n C (n + g) x = wireVal n C y x := by
          rw [hg_eval x, hvi, Bool.false_or]
        have hval := delGate_wireVal_eq n g y C x hRB hg hy_lt hmatch Cmid.output hCmid_out
        rw [hval, Bool.or_false]
        have hcfC : wireVal n C C.output x = F x := congrFun hF x
        by_cases ho : C.output = n + g
        · simp only [hCmid, delGate]
          rw [ho, origWire_remap_eq n g y hy_lt, ← hmatch, ← ho]
          exact hcfC
        · simp only [hCmid, delGate]
          rw [origWire_remap_ne n g y C.output ho]
          exact hcfC
      · rw [Bool.or_true]
        exact (hBelow x hvi).symm
    have hgateAt_lt : ∀ m < Cmid.gates.length,
        gateAt C' m = gateAt Cmid m := by
      intro m hm
      have hm' : m < C'.gates.length := by rw [hC'_len]; omega
      rw [gateAt_eq_getElem C' m hm', gateAt_eq_getElem Cmid m hm]
      simp [hC', pushOr, ← hCmid, List.getElem_append_left hm]
    have hgateAt_last : gateAt C' Cmid.gates.length = ⟨GateOp.or, [Cmid.output, n + i]⟩ := by
      have hm' : Cmid.gates.length < C'.gates.length := by rw [hC'_len]; omega
      rw [gateAt_eq_getElem C' Cmid.gates.length hm']
      simp [hC', pushOr, ← hCmid]
    have hop_shift : ∀ k < C.gates.length, k ≠ g →
        (gateAt C' (shiftDown g k)).op = (gateAt C k).op := by
      intro k hk hne
      have hsd : shiftDown g k < Cmid.gates.length := by
        unfold shiftDown; rw [hCmid_len]; split_ifs <;> omega
      rw [hgateAt_lt (shiftDown g k) hsd]
      rw [hCmid, delGate_gateAt n g y C hg (shiftDown g k) (by omega)]
      simp only [mapGate]
      have hidx : (if shiftDown g k < g then shiftDown g k else shiftDown g k + 1) = k := by
        unfold shiftDown; split_ifs <;> omega
      rw [hidx]
    have hsum : andIndexSum C' < andIndexSum C := by
      unfold andIndexSum
      set A := (Finset.range C.gates.length).filter (fun k => isAndOp (gateAt C k).op = true)
      set A' := (Finset.range C'.gates.length).filter (fun k => isAndOp (gateAt C' k).op = true)
      have hsum_eq : ∑ k ∈ A, shiftDown g k = ∑ m ∈ A', m := by
        apply Finset.sum_bij (fun k _ => shiftDown g k)
        · intro k hk
          simp only [A, A', Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff] at hk ⊢
          have hkne : k ≠ g := by
            intro hEq; rw [hEq, hgOr] at hk; cases hk.2
          have hsd_lt : shiftDown g k < C'.gates.length := by
            unfold shiftDown; rw [hC'_len]; split_ifs <;> omega
          exact ⟨hsd_lt, by rw [hop_shift k hk.1 hkne]; exact hk.2⟩
        · intro k1 hk1 k2 hk2 heq
          simp only [A, Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff] at hk1 hk2
          have hne1 : k1 ≠ g := by intro hEq; rw [hEq, hgOr] at hk1; cases hk1.2
          have hne2 : k2 ≠ g := by intro hEq; rw [hEq, hgOr] at hk2; cases hk2.2
          unfold shiftDown at heq
          split_ifs at heq <;> omega
        · intro m hm
          simp only [A', Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff] at hm
          have hm_ne : m ≠ Cmid.gates.length := by
            intro hEq; rw [hEq, hgateAt_last] at hm; cases hm.2
          have hm_mid : m < Cmid.gates.length := by rw [hC'_len] at hm; omega
          set k := if m < g then m else m + 1 with hk_def
          have hk_lt : k < C.gates.length := by rw [hk_def]; split_ifs <;> omega
          have hkne : k ≠ g := by rw [hk_def]; split_ifs <;> omega
          have hsd : shiftDown g k = m := by unfold shiftDown; rw [hk_def]; split_ifs <;> omega
          refine ⟨k, ?_, hsd⟩
          simp only [A, Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff]
          exact ⟨hk_lt, by rw [← hop_shift k hk_lt hkne, hsd]; exact hm.2⟩
        · intro _ _; rfl
      rw [← hsum_eq]
      apply Finset.sum_lt_sum
      · intro k _
        unfold shiftDown; split_ifs <;> omega
      · refine ⟨j, ?_, ?_⟩
        · simp only [A, Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff]
          exact ⟨hj, hjAnd⟩
        · unfold shiftDown; split_ifs <;> omega
    have hcount : andCount C' = andCount C := by
      unfold andCount
      symm
      apply Finset.card_bij (fun k _ => shiftDown g k)
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff] at hk ⊢
        have hne : k ≠ g := by intro he; rw [he, hgOr] at hk; cases hk.2
        have hslt : shiftDown g k < C'.gates.length := by
          unfold shiftDown; rw [hC'_len]; split_ifs <;> omega
        exact ⟨hslt, by rw [hop_shift k hk.1 hne]; exact hk.2⟩
      · intro k hk k' hk' he
        simp only [Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff] at hk hk'
        have hne : k ≠ g := by intro he; rw [he, hgOr] at hk; cases hk.2
        have hne' : k' ≠ g := by intro he; rw [he, hgOr] at hk'; cases hk'.2
        unfold shiftDown at he
        split_ifs at he <;> omega
      · intro m hm
        simp only [Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff] at hm
        have hmne : m ≠ Cmid.gates.length := by
          intro he; rw [he, hgateAt_last] at hm; cases hm.2
        have hm_mid : m < Cmid.gates.length := by rw [hC'_len] at hm; omega
        let k := if m < g then m else m+1
        have hk : k < C.gates.length := by unfold k; split_ifs <;> omega
        have hkne : k ≠ g := by unfold k; split_ifs <;> omega
        have hs : shiftDown g k = m := by unfold shiftDown k; split_ifs <;> omega
        refine ⟨k, ?_, hs⟩
        simp only [Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff]
        exact ⟨hk, by rw [←hop_shift k hk hkne, hs]; exact hm.2⟩
    have hinputs : (gateAt C g).inputs = [n+i,y] ∨ (gateAt C g).inputs = [y,n+i] := by
      rw [hgin, hy_def]
      split_ifs with ha
      · left; rw [ha]
      · right
        rcases hmem' with he | he
        · exact (ha he.symm).elim
        · rw [he]
    exact ⟨y, hy_lt, by simpa [hgin] using hinputs, hC'_AO, hC'_F, hC'_len, hcount, hsum⟩
  · simp [hgin] at hgin_len


lemma remap_lt (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length)
    (hr : r < n+g) (w : ℕ) (hw : w < n+C.gates.length) :
    remap n g r w < n+(delGate n g r C).gates.length := by
  rw [delGate_length n g r C hg]
  unfold remap
  split_ifs <;> omega

lemma delGate_wireVal_le (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hr : r < n+g)
    (hgr : wireVal n C r x = true → wireVal n C (n+g) x = true) :
    ∀ w < n+(delGate n g r C).gates.length,
      wireVal n (delGate n g r C) w x = true →
      wireVal n C (origWire n g w) x = true := by
  have hD := delGate_isAO2 n g r C hAO hg hr
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hv
    by_cases hwn : w < n
    · have ho : origWire n g w = w := by unfold origWire; split_ifs <;> omega
      rw [ho, wireVal_input n C x w hwn]
      rwa [wireVal_input n (delGate n g r C) x w hwn] at hv
    · let k := w-n
      have he : w = n+k := by unfold k; omega
      have hk : k < (delGate n g r C).gates.length := by omega
      have hk' : k < C.gates.length-1 := by rwa [delGate_length n g r C hg] at hk
      let k0 := if k < g then k else k+1
      have hk0 : k0 < C.gates.length := by unfold k0; split_ifs <;> omega
      have ho : origWire n g (n+k) = n+k0 := by
        unfold origWire k0; split_ifs <;> omega
      rw [he, wireVal_gate n (delGate n g r C) x k hk hD.2.1,
        delGate_gateAt n g r C hg k hk'] at hv
      rw [he, ho, wireVal_gate n C x k0 hk0 hAO.2.1]
      have hop : (gateAt C k0).op = .and ∨ (gateAt C k0).op = .or := by
        rw [gateAt_eq_getElem C k0 hk0]
        exact hAO.1 _ (List.getElem_mem hk0)
      simp only [mapGate, List.map_map] at hv
      change (gateAt C k0).op.eval ((gateAt C k0).inputs.map
        fun u => wireVal n (delGate n g r C) (remap n g r u) x) = true at hv
      apply gateOp_eval_mono (gateAt C k0).op hop _ _ (by simp) _ hv
      intro p hp1 hp2 hval
      simp only [List.getElem_map] at hval ⊢
      let u := (gateAt C k0).inputs[p]'(by simpa using hp2)
      have hu : u ∈ (gateAt C k0).inputs := List.getElem_mem (by simpa using hp2)
      have hru : remap n g r u < n+k := by
        apply hD.2.1 k hk
        rw [delGate_gateAt n g r C hg k hk']
        exact List.mem_map.mpr ⟨u,hu,rfl⟩
      have hih := ih (remap n g r u) (by omega) (by omega) hval
      change wireVal n C u x = true
      by_cases hug : u = n+g
      · rw [hug, origWire_remap_eq n g r hr] at hih
        rw [hug]
        exact hgr hih
      · rwa [origWire_remap_ne n g r u hug] at hih

lemma delGate_mapped_le (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hr : r < n+g)
    (hgr : wireVal n C r x = true → wireVal n C (n+g) x = true)
    (w : ℕ) (hw : w < n+C.gates.length) :
    wireVal n (delGate n g r C) (remap n g r w) x = true → wireVal n C w x = true := by
  intro hv
  have h := delGate_wireVal_le n g r C x hAO hg hr hgr
    (remap n g r w) (remap_lt n g r C hg hr w hw) hv
  by_cases he : w = n+g
  · rw [he, origWire_remap_eq n g r hr] at h
    rw [he]
    exact hgr h
  · rwa [origWire_remap_ne n g r w he] at h

lemma delGate_mapped_eq (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n+g)
    (hgr : wireVal n C (n+g) x = wireVal n C r x)
    (w : ℕ) (hw : w < n+C.gates.length) :
    wireVal n (delGate n g r C) (remap n g r w) x = wireVal n C w x := by
  rw [delGate_wireVal_eq n g r C x hRB hg hr hgr _ (remap_lt n g r C hg hr w hw)]
  by_cases he : w = n+g
  · rw [he, origWire_remap_eq n g r hr, hgr]
  · rw [origWire_remap_ne n g r w he]

lemma delGate_orIn (n g r : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hg : g < C.gates.length) (hr : r < n+g)
    (hgr : orIn n C (n+g) = orIn n C r) :
    ∀ w < n+(delGate n g r C).gates.length,
      orIn n (delGate n g r C) w = orIn n C (origWire n g w) := by
  classical
  have hD := delGate_isAO2 n g r C hAO hg hr
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · have ho : origWire n g w = w := by unfold origWire; split_ifs <;> omega
      rw [ho, H5Reach.orIn_input n C w hwn, H5Reach.orIn_input n (delGate n g r C) w hwn]
    · let k := w-n
      have he : w = n+k := by unfold k; omega
      have hk : k < (delGate n g r C).gates.length := by omega
      have hk' : k < C.gates.length-1 := by rwa [delGate_length n g r C hg] at hk
      let k0 := if k < g then k else k+1
      have hk0 : k0 < C.gates.length := by unfold k0; split_ifs <;> omega
      have ho : origWire n g (n+k) = n+k0 := by
        unfold origWire k0; split_ifs <;> omega
      rw [he, ho, H5Reach.orIn_gate n (delGate n g r C) hD.2.1 k hk,
        H5Reach.orIn_gate n C hAO.2.1 k0 hk0, delGate_gateAt n g r C hg k hk']
      simp only [mapGate]
      change (if (gateAt C k0).op = .or then
        ((gateAt C k0).inputs.map (remap n g r)).toFinset.biUnion
          (orIn n (delGate n g r C)) else ∅) =
        (if (gateAt C k0).op = .or then (gateAt C k0).inputs.toFinset.biUnion
          (orIn n C) else ∅)
      by_cases hop : (gateAt C k0).op = .or
      · simp only [hop, ↓reduceIte]
        have himg : ((gateAt C k0).inputs.map (remap n g r)).toFinset =
            (gateAt C k0).inputs.toFinset.image (remap n g r) := by
          ext u
          simp
        rw [himg, Finset.image_biUnion]
        apply Finset.biUnion_congr rfl
        intro u hu
        have hu' := List.mem_toFinset.mp hu
        have hru : remap n g r u < n+k := by
          apply hD.2.1 k hk
          rw [delGate_gateAt n g r C hg k hk']
          exact List.mem_map.mpr ⟨u,hu',rfl⟩
        rw [ih _ (by omega) (by omega)]
        by_cases hug : u = n+g
        · rw [hug, origWire_remap_eq n g r hr, hgr]
        · rw [origWire_remap_ne n g r u hug]
      · simp only [hop, ↓reduceIte]

lemma wireVal_monotone (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    ∀ w < n+C.gates.length, Monotone (wireVal n C w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw x y hxy
    apply Bool.le_iff_imp.mpr
    intro hv
    by_cases hwn : w < n
    · rw [wireVal_input n C x w hwn] at hv
      rw [wireVal_input n C y w hwn]
      exact Bool.le_iff_imp.mp (hxy ⟨w,hwn⟩) hv
    · let k := w-n
      have he : w = n+k := by unfold k; omega
      have hk : k < C.gates.length := by omega
      rw [he, wireVal_gate n C x k hk hAO.2.1] at hv
      rw [he, wireVal_gate n C y k hk hAO.2.1]
      have hop : (gateAt C k).op = .and ∨ (gateAt C k).op = .or := by
        rw [gateAt_eq_getElem C k hk]
        exact hAO.1 _ (List.getElem_mem hk)
      apply gateOp_eval_mono (gateAt C k).op hop _ _ (by simp) _ hv
      intro p hp1 hp2 hval
      simp only [List.getElem_map] at hval ⊢
      let u := (gateAt C k).inputs[p]'(by simpa using hp1)
      have hu : u < n+k := hAO.2.1 k hk u (List.getElem_mem (by simpa using hp1))
      exact Bool.le_iff_imp.mp (ih u (by omega) (by omega) hxy) hval

def singletonInput {n : ℕ} (a : Fin n) : Fin n → Bool :=
  fun b => decide (b = a)

def pureStar (n : ℕ) (C : Circuit) (w : ℕ) (Q : Finset (Fin n)) : Prop :=
  ∀ x : Fin n → Bool, wireVal n C w x = decide (∃ a ∈ Q, x a = true)

lemma delGate_pureStar (n g r : ℕ) (C : Circuit)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hr : r < n+g)
    (hle : ∀ x : Fin n → Bool, wireVal n C r x = true → wireVal n C (n+g) x = true)
    (hsingle : ∀ a : Fin n, wireVal n C (n+g) (singletonInput a) =
      wireVal n C r (singletonInput a))
    (w : ℕ) (hw : w < n+C.gates.length) (Q : Finset (Fin n)) (hQ : pureStar n C w Q) :
    pureStar n (delGate n g r C) (remap n g r w) Q := by
  have hD := delGate_isAO2 n g r C hAO hg hr
  have hwD := remap_lt n g r C hg hr w hw
  intro x
  cases hqx : decide (∃ a ∈ Q, x a = true) with
  | false =>
      cases hnew : wireVal n (delGate n g r C) (remap n g r w) x with
      | false => rfl
      | true =>
          have hOld := delGate_mapped_le n g r C x hAO hg hr (hle x) w hw hnew
          rw [hQ x, hqx] at hOld
          cases hOld
  | true =>
      obtain ⟨a, ha, hxa⟩ := of_decide_eq_true hqx
      have hpos : wireVal n (delGate n g r C) (remap n g r w) (singletonInput a) = true := by
        rw [delGate_mapped_eq n g r C (singletonInput a) hAO.2.1 hg hr (hsingle a) w hw,
          hQ (singletonInput a), decide_eq_true_eq]
        exact ⟨a, ha, by simp [singletonInput]⟩
      have hleX : singletonInput a ≤ x := by
        intro b
        by_cases hba : b = a
        · subst b; simp [singletonInput, hxa]
        · simp [singletonInput, hba]
      exact Bool.le_iff_imp.mp
        (wireVal_monotone n (delGate n g r C) hD _ hwD hleX) hpos

lemma or_reader_value (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (i g y : ℕ) (hg : g < C.gates.length) (hgOr : (gateAt C g).op = .or)
    (hinputs : (gateAt C g).inputs = [n+i,y] ∨ (gateAt C g).inputs = [y,n+i]) :
    ∀ x : Fin n → Bool,
      wireVal n C (n+g) x = (wireVal n C (n+i) x || wireVal n C y x) := by
  intro x
  rw [wireVal_gate n C x g hg hAO.2.1, hgOr]
  rcases hinputs with hi | hi
  · simp [hi, GateOp.eval]
  · simp [hi, GateOp.eval, Bool.or_comm]

lemma or_reader_reach (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (i g y : ℕ) (hig : i < g) (hg : g < C.gates.length)
    (hiAnd : (gateAt C i).op = .and) (hgOr : (gateAt C g).op = .or)
    (hinputs : (gateAt C g).inputs = [n+i,y] ∨ (gateAt C g).inputs = [y,n+i]) :
    orIn n C (n+g) = orIn n C y := by
  have hi : orIn n C (n+i) = ∅ := by
    rw [H5Reach.orIn_gate n C hAO.2.1 i (by omega)]
    simp [hiAnd]
  rw [H5Reach.orIn_gate n C hAO.2.1 g hg]
  rcases hinputs with h | h
  · simp [hgOr, h, hi]
  · simp [hgOr, h, hi]

lemma pushOr_pureStar (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (i g y : ℕ) (hg : g < C.gates.length) (hy : y < n+g)
    (hgOr : (gateAt C g).op = .or)
    (hinputs : (gateAt C g).inputs = [n+i,y] ∨ (gateAt C g).inputs = [y,n+i])
    (hi0 : ∀ a : Fin n, wireVal n C (n+i) (singletonInput a) = false)
    (w : ℕ) (hw : w < n+C.gates.length) (Q : Finset (Fin n)) (hQ : pureStar n C w Q) :
    pureStar n (pushOr n g y i C) (remap n g y w) Q := by
  have hreader := or_reader_value n C hAO i g y hg hgOr hinputs
  have hp := delGate_pureStar n g y C hAO hg hy
    (fun x hx => by rw [hreader x, hx, Bool.or_true])
    (fun a => by rw [hreader (singletonInput a), hi0 a, Bool.false_or]) w hw Q hQ
  intro x
  rw [show wireVal n (pushOr n g y i C) (remap n g y w) x =
      wireVal n (delGate n g y C) (remap n g y w) x from
    wireVal_append_lt n (delGate n g y C)
      ⟨.or,[(delGate n g y C).output,n+i]⟩
      (n+(delGate n g y C).gates.length) x (remap n g y w)
      (remap_lt n g y C hg hy w hw)]
  exact hp x

lemma orIn_append_lt (n : ℕ) (C : Circuit) (g : Gate) (out : ℕ)
    (hC : ReadsBack n C) (hD : ReadsBack n ⟨C.gates ++ [g],out⟩)
    (w : ℕ) (hw : w < n+C.gates.length) :
    orIn n ⟨C.gates ++ [g],out⟩ w = orIn n C w := by
  rw [←H5Reach.reachValues_eq_orIn n _ hD w,
    ←H5Reach.reachValues_eq_orIn n C hC w]
  rw [H5Reach.reachValues_append]
  apply List.getD_append
  rwa [H5Reach.reachValues_length]

lemma append_or_tCount_zero (n : ℕ) (C : Circuit) (lin : ℕ → Bool) (a b out : ℕ)
    (hC : ReadsBack n C) (ha : a < n+C.gates.length) (hb : b < n+C.gates.length)
    (hD : ReadsBack n ⟨C.gates ++ [⟨.or,[a,b]⟩],out⟩)
    (hT : PEqualNP.TwoColour.tCount n C lin = 0) (hb0 : orIn n C b = ∅) :
    PEqualNP.TwoColour.tCount n ⟨C.gates ++ [⟨.or,[a,b]⟩],out⟩ lin = 0 := by
  let D : Circuit := ⟨C.gates ++ [⟨.or,[a,b]⟩],out⟩
  apply (H5Reach.tCount_zero_iff_gate n D lin).mpr
  intro j hj hop u hu v hv
  by_cases hjC : j < C.gates.length
  · have hreach := orIn_append_lt n C ⟨.or,[a,b]⟩ out hC hD (n+j) (by omega)
    rw [hreach] at hu hv
    exact H5Reach.tCount_zero_all_wires n C lin hC hT (n+j) u hu v hv
  · have he : j = C.gates.length := by simp only [D, List.length_append, List.length_singleton] at hj; omega
    have hgat : gateAt D j = ⟨.or,[a,b]⟩ := by
      rw [gateAt_eq_getElem D j hj]
      simp [D, he]
    have hre : orIn n D (n+j) = orIn n C a := by
      rw [H5Reach.orIn_gate n D hD j hj, hgat]
      simp only [↓reduceIte, List.toFinset_cons, List.toFinset_nil,
        Finset.biUnion_insert, Finset.biUnion_empty, Finset.union_empty]
      rw [orIn_append_lt n C ⟨.or,[a,b]⟩ out hC hD a ha,
        orIn_append_lt n C ⟨.or,[a,b]⟩ out hC hD b hb, hb0, Finset.union_empty]
    rw [hre] at hu hv
    exact H5Reach.tCount_zero_all_wires n C lin hC hT a u hu v hv

lemma pushOr_tCount_zero (n : ℕ) (C : Circuit) (lin : ℕ → Bool)
    (hAO : IsAO2 n C) (hout : C.output < n+C.gates.length)
    (i g y : ℕ) (hig : i < g) (hg : g < C.gates.length) (hy : y < n+g)
    (hiAnd : (gateAt C i).op = .and) (hgOr : (gateAt C g).op = .or)
    (hinputs : (gateAt C g).inputs = [n+i,y] ∨ (gateAt C g).inputs = [y,n+i])
    (hD : IsAO2 n (pushOr n g y i C))
    (hT : PEqualNP.TwoColour.tCount n C lin = 0) :
    PEqualNP.TwoColour.tCount n (pushOr n g y i C) lin = 0 := by
  let M := delGate n g y C
  have hM := delGate_isAO2 n g y C hAO hg hy
  have hlen : M.gates.length = C.gates.length-1 := delGate_length n g y C hg
  have hr := or_reader_reach n C hAO i g y hig hg hiAnd hgOr hinputs
  have hTM : PEqualNP.TwoColour.tCount n M lin = 0 := by
    apply H5Reach.tCount_zero_of_orIn_subsets n C M lin hAO.2.1 hT
    intro j hj hop
    refine ⟨origWire n g (n+j), ?_⟩
    rw [delGate_orIn n g y C hAO hg hy hr (n+j) (by change n+j < n+M.gates.length; omega)]
  have hi0 : orIn n M (n+i) = ∅ := by
    rw [delGate_orIn n g y C hAO hg hy hr (n+i) (by change n+i < n+M.gates.length; omega)]
    have ho : origWire n g (n+i) = n+i := by unfold origWire; simp [hig]
    rw [ho, H5Reach.orIn_gate n C hAO.2.1 i (by omega)]
    simp [hiAnd]
  exact append_or_tCount_zero n M lin M.output (n+i) (n+M.gates.length) hM.2.1
    (delGate_output_lt n g y C hg hy hout) (by omega) hD.2.1 hTM hi0

end H5OrLift


namespace H5Minimum

lemma exists_minimizer {α : Type} (P : α → Prop) (f : α → ℕ)
    (h : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → f a ≤ f b := by
  classical
  have hex : ∃ k, ∃ a, P a ∧ f a = k := by
    obtain ⟨a, ha⟩ := h
    exact ⟨f a, a, ha, rfl⟩
  obtain ⟨a, ha, hfa⟩ := Nat.find_spec hex
  refine ⟨a, ha, ?_⟩
  intro b hb
  rw [hfa]
  exact Nat.find_min' hex ⟨b, hb, rfl⟩

lemma exists_three_minima {α : Type} (P : α → Prop) (f g h : α → ℕ)
    (hex : ∃ a, P a) :
    ∃ a, P a ∧ (∀ b, P b → f a ≤ f b) ∧
      (∀ b, P b → f b = f a → g a ≤ g b) ∧
      (∀ b, P b → f b = f a → g b = g a → h a ≤ h b) := by
  obtain ⟨a₀, ha₀, hmin₀⟩ := exists_minimizer P f hex
  obtain ⟨a₁, ⟨ha₁, heq₁⟩, hmin₁⟩ :=
    exists_minimizer (fun a => P a ∧ f a = f a₀) g ⟨a₀, ha₀, rfl⟩
  obtain ⟨a₂, ⟨ha₂, heq₂, heq₂g⟩, hmin₂⟩ :=
    exists_minimizer (fun a => P a ∧ f a = f a₀ ∧ g a = g a₁) h
      ⟨a₁, ha₁, heq₁, rfl⟩
  refine ⟨a₂, ha₂, ?_, ?_, ?_⟩
  · intro b hb
    rw [heq₂]
    exact hmin₀ b hb
  · intro b hb heq
    rw [heq₂g]
    exact hmin₁ b ⟨hb, heq.trans heq₂⟩
  · intro b hb heqf heqg
    exact hmin₂ b ⟨hb, heqf.trans heq₂, heqg.trans heq₂g⟩

end H5Minimum


namespace H5Count

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

lemma indexed_countP_eq {α : Type*} (gs : List α) (d : α) (p : α → Bool) :
    ((Finset.range gs.length).filter fun k => p (gs.getD k d) = true).card = gs.countP p := by
  have hmap : (List.range gs.length).map (fun k => gs.getD k d) = gs := by
    apply List.ext_getElem
    · simp
    · intro k hk hk'
      simp only [List.getElem_map, List.getElem_range]
      exact List.getD_eq_getElem _ _ hk'
  have h := (List.nodup_range : (List.range gs.length).Nodup).card_eq_countP
    (P := fun k => p (gs.getD k d) = true)
  have hrange : (List.range gs.length).toFinset = Finset.range gs.length := by
    ext k
    simp
  rw [hrange] at h
  calc
    ((Finset.range gs.length).filter fun k => p (gs.getD k d) = true).card =
        ((List.range gs.length).map (fun k => gs.getD k d)).countP p := by
      simpa [List.countP_map, Function.comp_def] using h
    _ = gs.countP p := by rw [hmap]

lemma indexed_andCount_eq (C : Circuit) :
    H5OrLift.andCount C = andCount C.gates := by
  simpa [H5OrLift.andCount, H5OrLift.isAndOp, andCount, isAndOp, gateAt] using
    indexed_countP_eq C.gates (⟨.or, []⟩ : Gate) (fun g => isAndOp g.op)

lemma output_valid_of_nonzero (n : ℕ) (C : Circuit)
    (hnonzero : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true) :
    C.output < n + C.gates.length := by
  obtain ⟨x,hx⟩ := hnonzero
  by_contra h
  have hz := H5Pruning.wireFn_ge n C C.output (by omega) x
  change C.eval (List.ofFn x) = false at hz
  rw [hx] at hz
  contradiction

end H5Count


namespace H5Stars

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.TwoColour
open H5Pruning H5Count H5AndTotal

def KeepsStars (n : ℕ) (C D : Circuit) : Prop :=
  ∀ (Q : Finset (Fin n)) (w : ℕ), 2 ≤ Q.card →
    (∀ x, wireFn n C w x = starFun Q x) →
      ∃ v : ℕ, ∀ x, wireFn n D v x = starFun Q x

lemma KeepsStars.refl (n : ℕ) (C : Circuit) : KeepsStars n C C := by
  intro Q w hQ hstar
  exact ⟨w, hstar⟩

lemma KeepsStars.trans {n : ℕ} {C D E : Circuit}
    (hCD : KeepsStars n C D) (hDE : KeepsStars n D E) : KeepsStars n C E := by
  intro Q w hQ hstar
  obtain ⟨v, hv⟩ := hCD Q w hQ hstar
  exact hDE Q v hQ hv

lemma keepsStars_of_or_roots (n : ℕ) (C D : Circuit)
    (h : ∀ (Q : Finset (Fin n)) (w : ℕ), 2 ≤ Q.card →
      (∀ x, wireFn n C w x = starFun Q x) →
      ∃ k < D.gates.length, (gateAt D k).op = .or ∧
        ∀ x, wireFn n D (n+k) x = starFun Q x) : KeepsStars n C D := by
  intro Q w hQ hstar
  obtain ⟨k, hk, hop, hval⟩ := h Q w hQ hstar
  exact ⟨n+k, hval⟩

lemma KeepsStars.or_root {n : ℕ} {C D : Circuit}
    (hCD : KeepsStars n C D) (hD : IsAO2 n D)
    (Q : Finset (Fin n)) (w : ℕ) (hQ : 2 ≤ Q.card)
    (hstar : ∀ x, wireFn n C w x = starFun Q x) :
    ∃ k < D.gates.length, (gateAt D k).op = .or ∧
      ∀ x, wireFn n D (n+k) x = starFun Q x := by
  obtain ⟨v, hv⟩ := hCD Q w hQ hstar
  exact pure_star_or_root n D hD Q hQ v hv

lemma and_reader_lift_keeps (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (F : (Fin n → Bool) → Bool) (hsingle : ∀ a : Fin n, F (singletonInput a) = false)
    (hspec : ∀ x, wireFn n C C.output x = F x)
    (i g : ℕ) (hg : g < C.gates.length) (hop : (gateAt C g).op = .and)
    (himem : i ∈ (gateAt C g).inputs)
    (hBelow : ∀ x, wireFn n C i x = true → F x = true)
    (lin : ℕ → Bool) (hT : tCount n C lin = 0) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ andCount D.gates < andCount C.gates ∧
      (∀ x, wireFn n D D.output x = F x) ∧ tCount n D lin = 0 ∧ KeepsStars n C D := by
  obtain ⟨D, hAO, hsize, hcount, hfun, hT, hstar⟩ :=
    and_reader_lift_total n C hC F hsingle hspec i g hg hop himem hBelow lin hT
  exact ⟨D, hAO, hsize, hcount, hfun, hT, keepsStars_of_or_roots n C D hstar⟩

lemma KeepsStars.served {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C D : Circuit) (hCD : KeepsStars (p+l) C D) (hD : IsAO2 (p+l) D)
    (hs : H5Bridge.served p l E C) : H5Bridge.served p l E D := by
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
    have hstar : ∀ x, wireFn (p+l) C (p+l+k) x = starFun Q' x := by
      intro x
      simpa [starFun,Q',wireFn] using hval x
    obtain ⟨k',hk',hop',hval'⟩ := hCD.or_root hD Q' (p+l+k) hc hstar
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
    have hstar : ∀ x, wireFn (p+l) C (p+l+k) x = starFun P' x := by
      intro x
      simpa [starFun,P',wireFn] using hval x
    obtain ⟨k',hk',hop',hval'⟩ := hCD.or_root hD P' (p+l+k) hc hstar
    refine ⟨k',P,hk',hop',hP,ha,hsub,?_⟩
    intro x
    simpa [starFun,P',wireFn] using hval' x

lemma admissible_of_keeps {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C D : Circuit) (hC : H5Bridge.admissible p l E C) (hD : IsAO2 (p+l) D)
    (hfun : ∀ x, wireFn (p+l) D D.output x = wireFn (p+l) C C.output x)
    (hT : tCount (p+l) D (fun i => decide (p ≤ i)) = 0)
    (hkeep : KeepsStars (p+l) C D) : H5Bridge.admissible p l E D := by
  refine ⟨hD, ?_, hT, KeepsStars.served E C D hkeep hD hC.2.2.2⟩
  intro x
  exact (hfun x).trans (hC.2.1 x)

end H5Stars


namespace H5OrLiftWrap

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.TwoColour
open H5Pruning H5Stars

lemma or_reader_lift_keeps (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (F : (Fin n → Bool) → Bool) (hsingle : ∀ a : Fin n, F (singletonInput a) = false)
    (hspec : ∀ x, wireFn n C C.output x = F x)
    (hout : C.output < n+C.gates.length)
    (i g j : ℕ) (hig : i < g) (hgj : g < j) (hj : j < C.gates.length)
    (hiAnd : (gateAt C i).op = .and) (hgOr : (gateAt C g).op = .or)
    (hjAnd : (gateAt C j).op = .and) (himem : n+i ∈ (gateAt C g).inputs)
    (hBelow : ∀ x, wireFn n C (n+i) x = true → F x = true)
    (lin : ℕ → Bool) (hT : tCount n C lin = 0) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size ∧
      H5Count.andCount D.gates = H5Count.andCount C.gates ∧
      (∀ x, wireFn n D D.output x = F x) ∧ tCount n D lin = 0 ∧
      KeepsStars n C D ∧ H5OrLift.andIndexSum D < H5OrLift.andIndexSum C := by
  have hF : circuitFun n C = F := funext hspec
  obtain ⟨y, hy, hinputs, hD, hFD, hsize, hcount, hindex⟩ :=
    H5OrLift.pushOr_step n F C i g j hC hF hout hig hgj hj hBelow hgOr hjAnd himem
  let D := H5OrLift.pushOr n g y i C
  have hcount' : H5Count.andCount D.gates = H5Count.andCount C.gates := by
    rw [←H5Count.indexed_andCount_eq D, ←H5Count.indexed_andCount_eq C]
    exact hcount
  have hi0 : ∀ a : Fin n, wireVal n C (n+i) (H5OrLift.singletonInput a) = false := by
    intro a
    cases hi : wireVal n C (n+i) (H5OrLift.singletonInput a) with
    | false => rfl
    | true =>
        have h := hBelow (H5OrLift.singletonInput a) hi
        change F (singletonInput a) = true at h
        rw [hsingle a] at h
        cases h
  refine ⟨D, hD, hsize, hcount', fun x => congrFun hFD x, ?_, ?_, hindex⟩
  · exact H5OrLift.pushOr_tCount_zero n C lin hC hout i g y hig (by omega) hy
      hiAnd hgOr hinputs hD hT
  · intro Q w hQ hstar
    have hw := pure_star_valid n C Q (Finset.card_pos.mp (by omega)) w hstar
    refine ⟨H5OrLift.remap n g y w, ?_⟩
    exact H5OrLift.pushOr_pureStar n C hC i g y (by omega) hy hgOr hinputs hi0
      w hw Q hstar

end H5OrLiftWrap


namespace H5Normalize

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open H5Pruning H5Stars

def good (n : ℕ) (F : (Fin n → Bool) → Bool) (lin : ℕ → Bool) (C : Circuit) : Prop :=
  IsAO2 n C ∧ (∀ x, wireFn n C C.output x = F x) ∧ PEqualNP.TwoColour.tCount n C lin = 0

def normal (n : ℕ) (F : (Fin n → Bool) → Bool) (C : Circuit) : Prop :=
  ∀ i < C.gates.length, ∀ j < C.gates.length,
    (gateAt C i).op = .and →
    (∀ x, wireFn n C (n+i) x = true → F x = true) →
    (gateAt C j).op = .and → ¬ InCone n C i j

lemma valid_output (n : ℕ) (F : (Fin n → Bool) → Bool) (C : Circuit)
    (hspec : ∀ x, wireFn n C C.output x = F x) (hpos : ∃ x, F x = true) :
    C.output < n + C.gates.length := by
  apply H5Count.output_valid_of_nonzero n C
  obtain ⟨x, hx⟩ := hpos
  exact ⟨x, (hspec x).trans hx⟩

lemma normalize_predicate (n : ℕ) (F : (Fin n → Bool) → Bool) (lin : ℕ → Bool)
    (hsingle : ∀ a : Fin n, F (singletonInput a) = false)
    (hpos : ∃ x, F x = true)
    (P : Circuit → Prop) (C : Circuit) (hC : P C)
    (hgood : ∀ D, P D → good n F lin D)
    (hclosed : ∀ D D', P D → good n F lin D' → KeepsStars n D D' → P D') :
    ∃ D, P D ∧ D.size ≤ C.size ∧ (∀ D', P D' → D.size ≤ D'.size) ∧ normal n F D := by
  classical
  obtain ⟨D, hD, hsize, hcount, hindex⟩ :=
    H5Minimum.exists_three_minima P Circuit.size
      (fun D => H5Count.andCount D.gates) H5OrLift.andIndexSum ⟨C, hC⟩
  refine ⟨D, hD, hsize C hC, hsize, ?_⟩
  obtain ⟨hAO, hspec, hT⟩ := hgood D hD
  intro i hi j hj hiAnd hBelow hjAnd hcone
  obtain ⟨g, hig, hgj, hg, hmem⟩ := H5OrLift.exists_direct_reader n D i j hj hcone
  have hgAO : (gateAt D g).op = GateOp.and ∨ (gateAt D g).op = GateOp.or := by
    rw [H5OrLift.gateAt_eq_getElem D g hg]
    exact hAO.1 D.gates[g] (List.getElem_mem hg)
  rcases hgAO with hgAnd | hgOr
  · obtain ⟨D', hAO', hsize', hcount', hspec', hT', hstars⟩ :=
      H5Stars.and_reader_lift_keeps n D hAO F hsingle hspec (n+i) g hg hgAnd hmem hBelow lin hT
    have hPD' : P D' := hclosed D D' hD ⟨hAO', hspec', hT'⟩ hstars
    have hsz : D'.size = D.size := Nat.le_antisymm hsize' (hsize D' hPD')
    have hcnt := hcount D' hPD' hsz
    omega
  · have hgj' : g < j := by
      by_contra hge
      have heq : g = j := by omega
      rw [heq, hjAnd] at hgOr
      cases hgOr
    obtain ⟨D', hAO', hsize', hcount', hspec', hT', hstars, hindex'⟩ :=
      H5OrLiftWrap.or_reader_lift_keeps n D hAO F hsingle hspec
        (valid_output n F D hspec hpos) i g j hig hgj' hj hiAnd hgOr hjAnd hmem hBelow lin hT
    have hPD' : P D' := hclosed D D' hD ⟨hAO', hspec', hT'⟩ hstars
    have hidx := hindex D' hPD' hsize' hcount'
    omega

lemma normalize_preserving (n : ℕ) (F : (Fin n → Bool) → Bool) (lin : ℕ → Bool)
    (hsingle : ∀ a : Fin n, F (singletonInput a) = false)
    (hpos : ∃ x, F x = true) (C : Circuit) (hC : good n F lin C) :
    ∃ D, good n F lin D ∧ D.size ≤ C.size ∧ KeepsStars n C D ∧ normal n F D := by
  let P := fun D => good n F lin D ∧ KeepsStars n C D
  obtain ⟨D, hD, hsize, _, hnormal⟩ := normalize_predicate n F lin hsingle hpos P C
    ⟨hC, KeepsStars.refl n C⟩ (fun _ h => h.1)
    (fun _ _ h hg hs => ⟨hg, KeepsStars.trans h.2 hs⟩)
  exact ⟨D, hD.1, hsize, hD.2, hnormal⟩

end H5Normalize


namespace H5Normalize

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open H5Pruning H5Stars H5Bridge

lemma bipartite_false_singletons {p l : ℕ} (E : Finset (Fin p × Fin l))
    (u : Fin (p+l)) : graphFun (bipartiteEdges E) (singletonInput u) = false := by
  rw [graphFun_bipartite]
  apply decide_eq_false
  rintro ⟨a, b, _, ha, hb⟩
  have ha' : Fin.castAdd l a = u := by simpa [singletonInput] using ha
  have hb' : Fin.natAdd p b = u := by simpa [singletonInput] using hb
  have heq := congrArg Fin.val (ha'.trans hb'.symm)
  simp only [Fin.val_castAdd, Fin.val_natAdd] at heq
  have hal := a.isLt
  omega

lemma exists_admissible_normal_edge_active {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : E.Nonempty) (C : Circuit) (hC : admissible p l E C) :
    ∃ D : Circuit, admissible p l E D ∧ D.size ≤ C.size ∧
      (∀ D', admissible p l E D' → D.size ≤ D'.size) ∧
      normal (p+l) (graphFun (bipartiteEdges E)) D ∧
      ∀ j < D.gates.length, ∃ (a : Fin p) (b : Fin l), (a,b) ∈ E ∧
        wireFn (p+l) D (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true := by
  classical
  let F := graphFun (bipartiteEdges E)
  have hpos : ∃ x, F x = true := by
    refine ⟨fun _ => true, ?_⟩
    rw [show F = graphFun (bipartiteEdges E) from rfl, graphFun_bipartite]
    obtain ⟨⟨a,b⟩,hab⟩ := hE
    exact decide_eq_true ⟨a,b,hab,rfl,rfl⟩
  have hgood : ∀ D, admissible p l E D → good (p+l) F (fun i => decide (p ≤ i)) D := by
    intro D hD
    refine ⟨hD.1, ?_, hD.2.2.1⟩
    intro x
    rw [show F x = graphFun (bipartiteEdges E) x from rfl, graphFun_bipartite]
    exact hD.2.1 x
  have hclosed : ∀ D D', admissible p l E D →
      good (p+l) F (fun i => decide (p ≤ i)) D' → KeepsStars (p+l) D D' →
      admissible p l E D' := by
    intro D D' hD hD' hstars
    apply admissible_of_keeps E D D' hD hD'.1 _ hD'.2.2 hstars
    intro x
    exact (hD'.2.1 x).trans ((hgood D hD).2.1 x).symm
  obtain ⟨D,hD,hsize,hmin,hN⟩ := normalize_predicate (p+l) F (fun i => decide (p ≤ i))
    (bipartite_false_singletons E) hpos (admissible p l E) C hC hgood hclosed
  refine ⟨D,hD,hsize,hmin,hN,?_⟩
  intro j hj
  by_contra hbad
  have hzero : ∀ a b, (a,b) ∈ E →
      wireFn (p+l) D (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = false := by
    intro a b hab
    cases hv : wireFn (p+l) D (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) with
    | false => rfl
    | true => exact False.elim (hbad ⟨a,b,hab,hv⟩)
  obtain ⟨D',hD',hlt⟩ := prune_admissible E hE D hD j hj hzero
  have hle := hmin D' hD'
  omega

end H5Normalize

namespace H5Essential

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.TwoColour
open H5Pruning H5Bridge H5Compile H5CompileReach H5LiftGlue H5AndTotal H5Stars H5Normalize

lemma graph_eq_of_positive_and_le (n : ℕ) (E : Finset (Fin n × Fin n))
    (f : (Fin n → Bool) → Bool) (hf : Monotone f)
    (hle : ∀ x, f x ≤ H5Pruning.graphFun E x)
    (hpos : ∀ e ∈ E, f (pairInput e.1 e.2) = true) :
    ∀ x, f x = H5Pruning.graphFun E x := by
  intro x
  cases hx : H5Pruning.graphFun E x with
  | false =>
      have h := hle x
      rw [hx] at h
      exact le_antisymm h (by cases f x <;> decide)
  | true =>
      obtain ⟨e, he, ha, hb⟩ := (of_decide_eq_true hx : ∃ e ∈ E, x e.1 = true ∧ x e.2 = true)
      have h := hf (pairInput_le e.1 e.2 x ha hb)
      exact Bool.le_iff_imp.mp h (hpos e he)

lemma changed_output_gate_true (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (x : Fin n → Bool) (hout : wireFn n C C.output x = true)
    (hzero : wireFn n (zeroed C j) C.output x = false) : wireFn n C (n+j) x = true := by
  cases hg : wireFn n C (n+j) x with
  | true => rfl
  | false =>
      have h := congrArg (fun w : List Bool => w.getD C.output false)
        (zeroed_eq_of_wire_false n C j hj x hg)
      change wireFn n (zeroed C j) C.output x = wireFn n C C.output x at h
      rw [hzero, hout] at h
      cases h

lemma zero_singleton_gate_essential {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : admissible p l E C)
    (hmin : ∀ D : Circuit, admissible p l E D → C.size ≤ D.size)
    (j : ℕ) (hj : j < C.gates.length)
    (hsingle : ∀ u : Fin (p+l), wireFn (p+l) C (p+l+j) (singletonInput u) = false) :
    ∃ (a : Fin p) (b : Fin l), (a,b) ∈ E ∧
      wireFn (p+l) C (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true ∧
      wireFn (p+l) (zeroed C j) C.output (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = false := by
  classical
  by_contra hbad
  have hspec : ∀ x, wireFn (p+l) C C.output x = H5Pruning.graphFun (bipartiteEdges E) x := by
    intro x
    rw [graphFun_bipartite]
    exact hC.2.1 x
  have hpos : ∀ a b, (a,b) ∈ E →
      wireFn (p+l) (zeroed C j) C.output (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true := by
    intro a b hab
    cases hz : wireFn (p+l) (zeroed C j) C.output (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) with
    | true => rfl
    | false =>
        have hout : wireFn (p+l) C C.output (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true := by
          rw [hspec, graphFun_bipartite]
          apply decide_eq_true
          exact ⟨a,b,hab,by simp [pairInput],by simp [pairInput]⟩
        have hgate := changed_output_gate_true (p+l) C j hj _ hout hz
        exact (hbad ⟨a,b,hab,hgate,hz⟩).elim
  have hfun0 : ∀ x, wireFn (p+l) (zeroed C j) C.output x = H5Pruning.graphFun (bipartiteEdges E) x := by
    apply graph_eq_of_positive_and_le (p+l) (bipartiteEdges E)
      (wireFn (p+l) (zeroed C j) C.output) (zeroed_wire_mono (p+l) C hC.1 j C.output)
    · intro x
      rw [← hspec x]
      exact zeroed_wire_le (p+l) C hC.1 j hj C.output x
    · intro e he
      obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp he
      exact hpos ab.1 ab.2 hab
  let C0 := zeroed C j
  let D := compiledCircuit (p+l) C0
  have hallowed : ∀ g ∈ C0.gates, allowed g := zeroed_allowed (p+l) C hC.1 j
  have hAO : IsAO2 (p+l) D := compiledCircuit_good (p+l) C0 hallowed
  have hfun : ∀ x, wireFn (p+l) D D.output x = wireFn (p+l) C C.output x := by
    intro x
    rw [show D = compiledCircuit (p+l) C0 from rfl, compiledCircuit_value (p+l) C0 hallowed]
    exact (hfun0 x).trans (hspec x).symm
  have hT0 : tCount (p+l) C0 (fun i => decide (p ≤ i)) = 0 :=
    zeroed_tCount (p+l) C j hj hC.1.2.1 _ hC.2.2.1
  have hTD : tCount (p+l) D (fun i => decide (p ≤ i)) = 0 :=
    compiled_tCount_zero (p+l) C0 D _ hallowed
      (zeroed_readsBack (p+l) C j hj hC.1.2.1) hT0 rfl
  have hstars : KeepsStars (p+l) C D := by
    intro Q w hQ hstar
    have hz : ∀ x, wireFn (p+l) C0 w x = starFun Q x :=
      zeroed_star_preserved_of_singletons (p+l) Q C hC.1 j hj (fun u _ => hsingle u) w hstar
    obtain ⟨k,hk,hop,hval⟩ := compiled_star (p+l) C0 D hallowed rfl hAO Q hQ w hz
    exact ⟨p+l+k,hval⟩
  have hD : admissible p l E D := admissible_of_keeps E C D hC hAO hfun hTD hstars
  have hsize : D.size < C.size :=
    lt_of_le_of_lt (compiledCircuit_size (p+l) C0) (zeroed_binaryCount_lt C j hj)
  have hle := hmin D hD
  omega

lemma safe_gate_essential {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : admissible p l E C)
    (hmin : ∀ D : Circuit, admissible p l E D → C.size ≤ D.size)
    (j : ℕ) (hj : j < C.gates.length)
    (hBelow : ∀ x, wireFn (p+l) C (p+l+j) x = true →
      H5Pruning.graphFun (bipartiteEdges E) x = true) :
    ∃ (a : Fin p) (b : Fin l), (a,b) ∈ E ∧
      wireFn (p+l) C (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true ∧
      wireFn (p+l) (zeroed C j) C.output (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = false := by
  apply zero_singleton_gate_essential E C hC hmin j hj
  exact wire_false_singletons_of_below (p+l) C (H5Pruning.graphFun (bipartiteEdges E))
    (bipartite_false_singletons E) (p+l+j) hBelow

lemma exists_admissible_normal_edge_active_essential {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : E.Nonempty) (C : Circuit) (hC : admissible p l E C) :
    ∃ D : Circuit, admissible p l E D ∧ D.size ≤ C.size ∧
      (∀ D', admissible p l E D' → D.size ≤ D'.size) ∧
      H5Normalize.normal (p+l) (H5Pruning.graphFun (bipartiteEdges E)) D ∧
      (∀ j < D.gates.length, ∃ (a : Fin p) (b : Fin l), (a,b) ∈ E ∧
        wireFn (p+l) D (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true) ∧
      ∀ j < D.gates.length,
        (∀ u : Fin (p+l), wireFn (p+l) D (p+l+j) (singletonInput u) = false) →
        ∃ (a : Fin p) (b : Fin l), (a,b) ∈ E ∧
          wireFn (p+l) D (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true ∧
          wireFn (p+l) (zeroed D j) D.output (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = false := by
  obtain ⟨D,hD,hsize,hmin,hnormal,hactive⟩ := exists_admissible_normal_edge_active E hE C hC
  refine ⟨D,hD,hsize,hmin,hnormal,hactive,?_⟩
  intro j hj hsingle
  exact zero_singleton_gate_essential E D hD hmin j hj hsingle

end H5Essential

-- P6 served-circuit minimum and an impure optimal control.
-- The lower bound uses AO2, exact computation, and semantic served-star witnesses;
-- it does not require T = 0. The eight-gate control also has T = 0 and every gate
-- is edge-active. It has an impure top-AND operand and minimizes both size and
-- AND count. It does NOT satisfy TopForm: its safe AND at index 3 is below the
-- AND at index 5. Thus this control makes no claim against a TopForm normalizer.

namespace H5Rectangles

def Rectangle {α β : Type*} [DecidableEq α] [DecidableEq β]
    (T : Finset (α × β)) : Prop :=
  ∃ A : Finset α, ∃ B : Finset β, T = A ×ˢ B

lemma rectangle_inter {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S T : Finset (α × β)} (hS : Rectangle S) (hT : Rectangle T) :
    Rectangle (S ∩ T) := by
  obtain ⟨A, B, rfl⟩ := hS
  obtain ⟨C, D, rfl⟩ := hT
  refine ⟨A ∩ C, B ∩ D, ?_⟩
  ext ⟨a, b⟩
  simp only [Finset.mem_inter, Finset.mem_product]
  tauto

lemma rectangle_empty {α β : Type*} [DecidableEq α] [DecidableEq β] :
    Rectangle (∅ : Finset (α × β)) :=
  ⟨∅, ∅, by simp⟩

lemma rectangle_univ {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] : Rectangle (Finset.univ : Finset (α × β)) := by
  refine ⟨Finset.univ, Finset.univ, ?_⟩
  ext ⟨a, b⟩
  simp

lemma rectangles_before_exception {α β : Type*} [DecidableEq α] [DecidableEq β]
    (N k : ℕ) (S : ℕ → Finset (α × β))
    (hstep : ∀ i < N, Rectangle (S i) ∨
      (∃ a b, a < i ∧ b < i ∧ S i = S a ∩ S b) ∨
      (i = k ∧ ∃ a b, a < i ∧ b < i ∧ S i = S a ∪ S b)) :
    ∀ i < N, i < k → Rectangle (S i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi hik
    rcases hstep i hi with hR | hI | ⟨rfl, hU⟩
    · exact hR
    · obtain ⟨a, b, ha, hb, heq⟩ := hI
      rw [heq]
      exact rectangle_inter (ih a ha (by omega) (by omega))
        (ih b hb (by omega) (by omega))
    · omega

lemma single_exception_factor {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (N k : ℕ) (S : ℕ → Finset (α × β))
    (hstep : ∀ i < N, Rectangle (S i) ∨
      (∃ a b, a < i ∧ b < i ∧ S i = S a ∩ S b) ∨
      (i = k ∧ ∃ a b, a < i ∧ b < i ∧ S i = S a ∪ S b)) :
    ∀ i < N, ∃ R : Finset (α × β), Rectangle R ∧
      (S i = R ∨ S i = S k ∩ R) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    rcases hstep i hi with hR | hI | ⟨rfl, hU⟩
    · exact ⟨S i, hR, Or.inl rfl⟩
    · obtain ⟨a, b, ha, hb, hI⟩ := hI
      obtain ⟨A, hA, hAS⟩ := ih a ha (by omega)
      obtain ⟨B, hB, hBS⟩ := ih b hb (by omega)
      refine ⟨A ∩ B, rectangle_inter hA hB, ?_⟩
      rcases hAS with hAS | hAS <;> rcases hBS with hBS | hBS
      · left
        rw [hI, hAS, hBS]
      · right
        rw [hI, hAS, hBS]
        ext x
        simp only [Finset.mem_inter]
        tauto
      · right
        rw [hI, hAS, hBS]
        ext x
        simp only [Finset.mem_inter]
        tauto
      · right
        rw [hI, hAS, hBS]
        ext x
        simp only [Finset.mem_inter]
        tauto
    · exact ⟨Finset.univ, rectangle_univ, Or.inr (by simp)⟩

lemma one_exception_two_rectangles {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (N k : ℕ) (S : ℕ → Finset (α × β))
    (hstep : ∀ i < N, Rectangle (S i) ∨
      (∃ a b, a < i ∧ b < i ∧ S i = S a ∩ S b) ∨
      (i = k ∧ ∃ a b, a < i ∧ b < i ∧ S i = S a ∪ S b)) :
    ∀ i < N, ∃ A B : Finset (α × β), Rectangle A ∧ Rectangle B ∧ S i = A ∪ B := by
  intro i hi
  by_cases hk : k < N
  · have hK : ∃ A B : Finset (α × β), Rectangle A ∧ Rectangle B ∧ S k = A ∪ B := by
      rcases hstep k hk with hR | hI | ⟨hkk, hU⟩
      · exact ⟨S k, ∅, hR, rectangle_empty, by simp⟩
      · obtain ⟨a, b, ha, hb, heq⟩ := hI
        have hR : Rectangle (S k) := by
          rw [heq]
          exact rectangle_inter
            (rectangles_before_exception N k S hstep a (by omega) ha)
            (rectangles_before_exception N k S hstep b (by omega) hb)
        exact ⟨S k, ∅, hR, rectangle_empty, by simp⟩
      · obtain ⟨a, b, ha, hb, heq⟩ := hU
        exact ⟨S a, S b,
          rectangles_before_exception N k S hstep a (by omega) ha,
          rectangles_before_exception N k S hstep b (by omega) hb, heq⟩
    obtain ⟨A, B, hA, hB, hK⟩ := hK
    obtain ⟨R, hR, heq | heq⟩ := single_exception_factor N k S hstep i hi
    · exact ⟨R, ∅, hR, rectangle_empty, by simpa using heq⟩
    · refine ⟨A ∩ R, B ∩ R, rectangle_inter hA hR, rectangle_inter hB hR, ?_⟩
      rw [heq, hK]
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      tauto
  · have hR := rectangles_before_exception N k S hstep i hi (by omega)
    exact ⟨S i, ∅, hR, rectangle_empty, by simp⟩

def pathEdges : Finset (Fin 3 × Fin 3) := {(0, 0), (1, 0), (1, 1), (2, 1), (2, 2)}

lemma path_not_two_rectangles : ¬ ∃ (A B C D : Finset (Fin 3)),
    pathEdges = (A ×ˢ B) ∪ (C ×ˢ D) := by
  decide +kernel

lemma path_not_two_rectangles' : ¬ ∃ A B : Finset (Fin 3 × Fin 3),
    Rectangle A ∧ Rectangle B ∧ pathEdges = A ∪ B := by
  rintro ⟨A, B, ⟨P, Q, rfl⟩, ⟨R, T, rfl⟩, h⟩
  exact path_not_two_rectangles ⟨P, Q, R, T, h⟩

end H5Rectangles

namespace H5Rectangles

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.Outside.L_meta_4970_aux.H5Pruning

def pair (a b : Fin 3) : Fin 6 → Bool :=
  fun i => decide (i = Fin.castAdd 3 a ∨ i = Fin.natAdd 3 b)

def table (C : Circuit) (w : ℕ) : Finset (Fin 3 × Fin 3) :=
  Finset.univ.filter fun ab => wireFn 6 C w (pair ab.1 ab.2) = true

lemma pair_left (a b u : Fin 3) : pair a b (Fin.castAdd 3 u) = decide (u = a) := by
  fin_cases a <;> fin_cases b <;> fin_cases u <;> decide +kernel

lemma pair_right (a b u : Fin 3) : pair a b (Fin.natAdd 3 u) = decide (u = b) := by
  fin_cases a <;> fin_cases b <;> fin_cases u <;> decide +kernel

lemma pair_addNat (a b u : Fin 3) : pair a b (u.addNat 3) = decide (u = b) := by
  fin_cases a <;> fin_cases b <;> fin_cases u <;> decide +kernel

lemma input_rectangle (C : Circuit) (i : ℕ) (hi : i < 6) : Rectangle (table C i) := by
  have heq : table C i = Finset.univ.filter
      (fun ab : Fin 3 × Fin 3 => pair ab.1 ab.2 ⟨i, hi⟩ = true) := by
    ext ab
    simp [table, wireFn_input 6 C i hi]
  rw [heq]
  have hbase : ∀ u : Fin 6, Rectangle
      (Finset.univ.filter (fun ab : Fin 3 × Fin 3 => pair ab.1 ab.2 u = true)) := by
    unfold Rectangle
    decide +kernel
  exact hbase ⟨i, hi⟩

lemma left_pure_rectangle (C : Circuit) (j : ℕ) (P : Finset (Fin 3))
    (h : ∀ x : Fin 6 → Bool, wireFn 6 C (6 + j) x =
      decide (∃ a ∈ P, x (Fin.castAdd 3 a) = true)) : Rectangle (table C (6 + j)) := by
  refine ⟨P, Finset.univ, ?_⟩
  ext ⟨a, b⟩
  simp [table, h, pair_left]

lemma right_pure_rectangle (C : Circuit) (j : ℕ) (Q : Finset (Fin 3))
    (h : ∀ x : Fin 6 → Bool, wireFn 6 C (6 + j) x =
      decide (∃ b ∈ Q, x (Fin.natAdd 3 b) = true)) : Rectangle (table C (6 + j)) := by
  refine ⟨Finset.univ, Q, ?_⟩
  ext ⟨a, b⟩
  simp [table, h, pair_addNat]

lemma table_binary (C : Circuit) (hC : IsAO2 6 C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, a < 6 + j ∧ b < 6 + j ∧
      (((gateAt C j).op = GateOp.and ∧ table C (6 + j) = table C a ∩ table C b) ∨
      ((gateAt C j).op = GateOp.or ∧ table C (6 + j) = table C a ∪ table C b)) := by
  obtain ⟨a, b, ha, hb, hab, hop, he⟩ := binary_gate 6 C hC j hj
  refine ⟨a, b, ha, hb, ?_⟩
  rcases hop with hop | hop
  · left
    refine ⟨hop, ?_⟩
    ext ⟨u, v⟩
    simp [table, he, hop, GateOp.eval]
  · right
    refine ⟨hop, ?_⟩
    ext ⟨u, v⟩
    simp [table, he, hop, GateOp.eval]

lemma circuit_one_exception (C : Circuit) (hC : IsAO2 6 C) (k : ℕ)
    (hOR : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      j ≠ k → Rectangle (table C (6 + j))) :
    ∀ w < 6 + C.gates.length, ∃ A B : Finset (Fin 3 × Fin 3),
      Rectangle A ∧ Rectangle B ∧ table C w = A ∪ B := by
  apply one_exception_two_rectangles (6 + C.gates.length) (6 + k) (table C)
  intro w hw
  by_cases hin : w < 6
  · exact Or.inl (input_rectangle C w hin)
  · let j := w - 6
    have hwj : w = 6 + j := by dsimp [j]; omega
    have hj : j < C.gates.length := by omega
    obtain ⟨a, b, ha, hb, hA | hO⟩ := table_binary C hC j hj
    · right
      left
      exact ⟨a, b, by omega, by omega, by simpa [hwj] using hA.2⟩
    · by_cases hjk : j = k
      · right
        right
        exact ⟨by omega, a, b, by omega, by omega, by simpa [hwj] using hO.2⟩
      · left
        simpa [hwj] using hOR j hj hO.1 hjk

def computesPath (C : Circuit) : Prop :=
  ∀ x : Fin 6 → Bool, circuitFun 6 C x =
    decide (∃ (a : Fin 3) (b : Fin 3), (a, b) ∈ pathEdges ∧
      x (Fin.castAdd 3 a) = true ∧ x (Fin.natAdd 3 b) = true)

lemma path_output_valid (C : Circuit) (hF : computesPath C) :
    C.output < 6 + C.gates.length := by
  by_contra h
  have hz := wireFn_ge 6 C C.output (by omega) (pair 0 0)
  have hf := hF (pair 0 0)
  change wireFn 6 C C.output (pair 0 0) = _ at hf
  rw [hz] at hf
  have ht : decide (∃ (a : Fin 3) (b : Fin 3), (a, b) ∈ pathEdges ∧
      pair 0 0 (Fin.castAdd 3 a) = true ∧ pair 0 0 (Fin.natAdd 3 b) = true) = true := by
    decide +kernel
  rw [ht] at hf
  contradiction

lemma path_output_table (C : Circuit) (hF : computesPath C) : table C C.output = pathEdges := by
  ext ⟨a, b⟩
  have h : wireFn 6 C C.output (pair a b) =
    decide (∃ (u : Fin 3) (v : Fin 3), (u, v) ∈ pathEdges ∧
      pair a b (Fin.castAdd 3 u) = true ∧ pair a b (Fin.natAdd 3 v) = true) := hF _
  simp [table, h, pair_left, pair_addNat]

noncomputable def orGates (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun j => (gateAt C j).op = GateOp.or

lemma orGates_mem (C : Circuit) (j : ℕ) :
    j ∈ orGates C ↔ j < C.gates.length ∧ (gateAt C j).op = GateOp.or := by
  classical
  simp [orGates]

lemma path_three_rectangular_ors (C : Circuit) (hC : IsAO2 6 C) (hF : computesPath C)
    (W : Finset ℕ) (hW : W ⊆ orGates C) (hcard : W.card = 3)
    (hrect : ∀ j ∈ W, Rectangle (table C (6 + j))) : 5 ≤ (orGates C).card := by
  classical
  by_contra hlt
  let R := orGates C \ W
  have hR : R.card ≤ 1 := by
    dsimp [R]
    rw [Finset.card_sdiff_of_subset hW, hcard]
    omega
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ j ∈ R, j = k := by
    by_cases hempty : R = ∅
    · exact ⟨0, by simp [hempty]⟩
    · obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      refine ⟨k, ?_⟩
      intro j hj
      exact Finset.card_le_one.mp hR j hj k hk
  have hOR : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      j ≠ k → Rectangle (table C (6 + j)) := by
    intro j hj hop hne
    have hm : j ∈ orGates C := (orGates_mem C j).mpr ⟨hj, hop⟩
    by_cases hw : j ∈ W
    · exact hrect j hw
    · exact False.elim (hne (hk j (Finset.mem_sdiff.mpr ⟨hm, hw⟩)))
  obtain ⟨A, B, hA, hB, heq⟩ := circuit_one_exception C hC k hOR C.output (path_output_valid C hF)
  rw [path_output_table C hF] at heq
  exact path_not_two_rectangles' ⟨A, B, hA, hB, heq⟩

def servedPath (C : Circuit) : Prop :=
  ∀ (a b : Fin 3), (a, b) ∈ pathEdges →
    (∃ (j : ℕ) (Q : Finset (Fin 3)), j < C.gates.length ∧
      (gateAt C j).op = GateOp.or ∧ 2 ≤ Q.card ∧ b ∈ Q ∧
      (∀ b' ∈ Q, (a, b') ∈ pathEdges) ∧ ∀ x : Fin 6 → Bool,
        wireFn 6 C (6 + j) x = decide (∃ b' ∈ Q, x (Fin.natAdd 3 b') = true)) ∨
    (∃ (j : ℕ) (P : Finset (Fin 3)), j < C.gates.length ∧
      (gateAt C j).op = GateOp.or ∧ 2 ≤ P.card ∧ a ∈ P ∧
      (∀ a' ∈ P, (a', b) ∈ pathEdges) ∧ ∀ x : Fin 6 → Bool,
        wireFn 6 C (6 + j) x = decide (∃ a' ∈ P, x (Fin.castAdd 3 a') = true))

lemma no_left_zero : ∀ Q : Finset (Fin 3), 2 ≤ Q.card →
    (∀ b ∈ Q, ((0 : Fin 3), b) ∈ pathEdges) → False := by
  decide +kernel

lemma no_right_two : ∀ P : Finset (Fin 3), 2 ≤ P.card →
    (∀ a ∈ P, (a, (2 : Fin 3)) ∈ pathEdges) → False := by
  decide +kernel

lemma left_one : ∀ Q : Finset (Fin 3), 2 ≤ Q.card →
    (∀ b ∈ Q, ((1 : Fin 3), b) ∈ pathEdges) → Q = {0, 1} := by
  decide +kernel

lemma left_two : ∀ Q : Finset (Fin 3), 2 ≤ Q.card →
    (∀ b ∈ Q, ((2 : Fin 3), b) ∈ pathEdges) → Q = {1, 2} := by
  decide +kernel

lemma right_zero : ∀ P : Finset (Fin 3), 2 ≤ P.card →
    (∀ a ∈ P, (a, (0 : Fin 3)) ∈ pathEdges) → P = {0, 1} := by
  decide +kernel

lemma right_one : ∀ P : Finset (Fin 3), 2 ≤ P.card →
    (∀ a ∈ P, (a, (1 : Fin 3)) ∈ pathEdges) → P = {1, 2} := by
  decide +kernel

def unit (i : Fin 6) : Fin 6 → Bool := fun k => decide (k = i)

lemma first_witness (C : Circuit) (hs : servedPath C) :
    ∃ j ∈ orGates C, Rectangle (table C (6 + j)) ∧
      wireFn 6 C (6 + j) (unit 0) = true ∧ wireFn 6 C (6 + j) (unit 5) = false := by
  rcases hs 0 0 (by decide +kernel) with ⟨j, Q, hj, hop, hQ, hb, hsub, hval⟩ |
    ⟨j, P, hj, hop, hP, ha, hsub, hval⟩
  · exact False.elim (no_left_zero Q hQ hsub)
  · have hP := right_zero P hP hsub
    subst P
    refine ⟨j, (orGates_mem C j).mpr ⟨hj, hop⟩, left_pure_rectangle C j {0, 1} hval, ?_, ?_⟩
    · rw [hval]
      decide +kernel
    · rw [hval]
      decide +kernel

lemma last_witness (C : Circuit) (hs : servedPath C) :
    ∃ j ∈ orGates C, Rectangle (table C (6 + j)) ∧
      wireFn 6 C (6 + j) (unit 0) = false ∧ wireFn 6 C (6 + j) (unit 5) = true := by
  rcases hs 2 2 (by decide +kernel) with ⟨j, Q, hj, hop, hQ, hb, hsub, hval⟩ |
    ⟨j, P, hj, hop, hP, ha, hsub, hval⟩
  · have hQ := left_two Q hQ hsub
    subst Q
    refine ⟨j, (orGates_mem C j).mpr ⟨hj, hop⟩, right_pure_rectangle C j {1, 2} hval, ?_, ?_⟩
    · rw [hval]
      decide +kernel
    · rw [hval]
      decide +kernel
  · exact False.elim (no_right_two P hP hsub)

lemma middle_witness (C : Circuit) (hs : servedPath C) :
    ∃ j ∈ orGates C, Rectangle (table C (6 + j)) ∧
      wireFn 6 C (6 + j) (unit 0) = false ∧ wireFn 6 C (6 + j) (unit 5) = false := by
  rcases hs 1 1 (by decide +kernel) with ⟨j, Q, hj, hop, hQ, hb, hsub, hval⟩ |
    ⟨j, P, hj, hop, hP, ha, hsub, hval⟩
  · have hQ := left_one Q hQ hsub
    subst Q
    refine ⟨j, (orGates_mem C j).mpr ⟨hj, hop⟩, right_pure_rectangle C j {0, 1} hval, ?_, ?_⟩
    · rw [hval]
      decide +kernel
    · rw [hval]
      decide +kernel
  · have hP := right_one P hP hsub
    subst P
    refine ⟨j, (orGates_mem C j).mpr ⟨hj, hop⟩, left_pure_rectangle C j {1, 2} hval, ?_, ?_⟩
    · rw [hval]
      decide +kernel
    · rw [hval]
      decide +kernel

lemma path_or_count (C : Circuit) (hC : IsAO2 6 C) (hF : computesPath C)
    (hs : servedPath C) : 5 ≤ (orGates C).card := by
  classical
  obtain ⟨i, hi, hRi, hi0, hi5⟩ := first_witness C hs
  obtain ⟨j, hj, hRj, hj0, hj5⟩ := last_witness C hs
  obtain ⟨k, hk, hRk, hk0, hk5⟩ := middle_witness C hs
  have hij : i ≠ j := by
    intro h
    subst j
    rw [hi0] at hj0
    contradiction
  have hik : i ≠ k := by
    intro h
    subst k
    rw [hi0] at hk0
    contradiction
  have hjk : j ≠ k := by
    intro h
    subst k
    rw [hj5] at hk5
    contradiction
  apply path_three_rectangular_ors C hC hF {i, j, k}
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hi
    · exact hj
    · exact hk
  · simp [hij, hik, hjk]
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hRi
    · exact hRj
    · exact hRk

end H5Rectangles

namespace H5AndCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  H5Pruning

def andGates (C : Circuit) : Finset (Fin C.gates.length) := by
  letI : DecidableEq GateOp := gateOpDecEq
  exact Finset.univ.filter fun j => (gateAt C j.val).op = GateOp.and

lemma mem_andGates (C : Circuit) (j : Fin C.gates.length) :
    j ∈ andGates C ↔ (gateAt C j.val).op = GateOp.and := by
  simp [andGates]

def andNatGates (C : Circuit) : Finset ℕ := by
  letI : DecidableEq GateOp := gateOpDecEq
  exact (Finset.range C.gates.length).filter fun j => (gateAt C j).op = GateOp.and

lemma mem_andNatGates (C : Circuit) (j : ℕ) :
    j ∈ andNatGates C ↔ j < C.gates.length ∧ (gateAt C j).op = GateOp.and := by
  simp [andNatGates]

lemma andGates_image_val (C : Circuit) :
    (andGates C).image (fun j => j.val) = andNatGates C := by
  ext j
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
    exact (mem_andNatGates C i.val).mpr ⟨i.isLt, (mem_andGates C i).mp hi⟩
  · intro h
    obtain ⟨hj, hop⟩ := (mem_andNatGates C j).mp h
    exact Finset.mem_image.mpr ⟨⟨j, hj⟩, (mem_andGates C ⟨j, hj⟩).mpr hop, rfl⟩

lemma andGates_card_nat (C : Circuit) : (andGates C).card = (andNatGates C).card := by
  rw [← andGates_image_val]
  exact (Finset.card_image_of_injective (andGates C) Fin.val_injective).symm

def signature (n : ℕ) (C : Circuit) (x : Fin n → Bool) : ↥(andGates C) → Bool :=
  fun j => wireFn n C (opnd C j.val.val 0) x

lemma same_signature_join_false (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (x y : Fin n → Bool) (hs : signature n C x = signature n C y) :
    ∀ w, wireFn n C w x = false → wireFn n C w y = false →
      wireFn n C w (fun i => x i || y i) = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hx hy
    by_cases hinput : w < n
    · rw [wireFn_input n C w hinput] at hx hy ⊢
      simp [hx, hy]
    by_cases hvalid : w < n + C.gates.length
    · let j := w - n
      have hj : j < C.gates.length := by dsimp [j]; omega
      have hjw : n + j = w := by dsimp [j]; omega
      obtain ⟨a, b, ha, hb, hab, hop, he⟩ := binary_gate n C hC j hj
      have ha' : a < w := by omega
      have hb' : b < w := by omega
      rcases hop with hop | hop
      · have hmem : (⟨j, hj⟩ : Fin C.gates.length) ∈ andGates C :=
          (mem_andGates C ⟨j, hj⟩).mpr hop
        have hs' := congrFun hs ⟨⟨j, hj⟩, hmem⟩
        change wireFn n C (opnd C j 0) x = wireFn n C (opnd C j 0) y at hs'
        have hopnd : opnd C j 0 = a := by simp [opnd, hab]
        rw [hopnd] at hs'
        have hx' : (wireFn n C a x && wireFn n C b x) = false := by
          have h := he x
          rw [hjw, hx, hop] at h
          simpa [GateOp.eval] using h.symm
        have hy' : (wireFn n C a y && wireFn n C b y) = false := by
          have h := he y
          rw [hjw, hy, hop] at h
          simpa [GateOp.eval] using h.symm
        have hout := he (fun i => x i || y i)
        rw [hjw, hop] at hout
        cases hax : wireFn n C a x with
        | false =>
          have hay : wireFn n C a y = false := hs'.symm.trans hax
          have haz := ih a ha' hax hay
          simpa [GateOp.eval, haz] using hout
        | true =>
          have hay : wireFn n C a y = true := hs'.symm.trans hax
          have hbx : wireFn n C b x = false := by simpa [hax] using hx'
          have hby : wireFn n C b y = false := by simpa [hay] using hy'
          have hbz := ih b hb' hbx hby
          simpa [GateOp.eval, hbz] using hout
      · have hx' : wireFn n C a x = false ∧ wireFn n C b x = false := by
          have h := he x
          rw [hjw, hx, hop] at h
          simpa [GateOp.eval] using h.symm
        have hy' : wireFn n C a y = false ∧ wireFn n C b y = false := by
          have h := he y
          rw [hjw, hy, hop] at h
          simpa [GateOp.eval] using h.symm
        have haz := ih a ha' hx'.1 hy'.1
        have hbz := ih b hb' hx'.2 hy'.2
        have hout := he (fun i => x i || y i)
        rw [hjw, hop] at hout
        simpa [GateOp.eval, haz, hbz] using hout
    · exact wireFn_ge n C w (by omega) _

lemma false_family_and_bound (n m : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (inputs : Fin m → Fin n → Bool)
    (hfalse : ∀ i, wireFn n C C.output (inputs i) = false)
    (hjoin : ∀ i j, i ≠ j →
      wireFn n C C.output (fun k => inputs i k || inputs j k) = true) :
    m ≤ 2 ^ (andGates C).card := by
  classical
  have hinj : Function.Injective (fun i => signature n C (inputs i)) := by
    intro i j hs
    by_contra hij
    have hz := same_signature_join_false n C hC (inputs i) (inputs j) hs
      C.output (hfalse i) (hfalse j)
    have ht := hjoin i j hij
    simp [hz] at ht
  have hc := Fintype.card_le_of_injective (fun i => signature n C (inputs i)) hinj
  simpa using hc

def pathFun (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 3) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 4) || (x 2 && x 5)

def negativeInput (i : Fin 5) (v : Fin 6) : Bool :=
  (([7, 12, 35, 49, 56] : List ℕ).getD i.val 0).testBit v.val

lemma negative_false : ∀ i : Fin 5, pathFun (negativeInput i) = false := by
  decide +kernel

lemma negative_join_true : ∀ i j : Fin 5, i ≠ j →
    pathFun (fun k => negativeInput i k || negativeInput j k) = true := by
  decide +kernel

lemma path_and_count (C : Circuit) (hC : IsAO2 6 C)
    (hF : ∀ x : Fin 6 → Bool, PEqualNP.MetaComplexity.circuitFun 6 C x = pathFun x) :
    3 ≤ (andGates C).card := by
  have hwire : ∀ x : Fin 6 → Bool, wireFn 6 C C.output x = pathFun x := hF
  have hb := false_family_and_bound 6 5 C hC negativeInput
    (fun i => by rw [hwire]; exact negative_false i)
    (fun i j hij => by rw [hwire]; exact negative_join_true i j hij)
  by_contra hn
  have hle : (andGates C).card ≤ 2 := by omega
  interval_cases hq : (andGates C).card <;> norm_num [hq] at hb

lemma path_and_count_nat (C : Circuit) (hC : IsAO2 6 C)
    (hF : ∀ x : Fin 6 → Bool, PEqualNP.MetaComplexity.circuitFun 6 C x = pathFun x) :
    3 ≤ (andNatGates C).card := by
  rw [← andGates_card_nat]
  exact path_and_count C hC hF

end H5AndCount

namespace H5Rectangles

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.Outside.L_meta_4970_aux.H5Pruning
  PEqualNP.Outside.L_meta_4970_aux.H5AndCount

lemma gate_count_partition (C : Circuit) (hC : IsAO2 6 C) :
    (andNatGates C).card + (orGates C).card = C.gates.length := by
  classical
  have hd : Disjoint (andNatGates C) (orGates C) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    have ha := (mem_andNatGates C j).mp hj
    have ho := (orGates_mem C j).mp hk
    rw [ha.2] at ho
    cases ho.2
  have hu : andNatGates C ∪ orGates C = Finset.range C.gates.length := by
    ext j
    simp only [Finset.mem_union, mem_andNatGates, orGates_mem, Finset.mem_range]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hj
      obtain ⟨a, b, ha, hb, hab, hop, he⟩ :=
        PEqualNP.Outside.L_meta_4970_aux.H5Pruning.binary_gate 6 C hC j hj
      rcases hop with ha | ho
      · exact Or.inl ⟨hj, ha⟩
      · exact Or.inr ⟨hj, ho⟩
  rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_range]

lemma path_computes_explicit (C : Circuit) (hF : computesPath C) :
    ∀ x : Fin 6 → Bool, circuitFun 6 C x = pathFun x := by
  have h : ∀ x : Fin 6 → Bool,
      decide (∃ (a b : Fin 3), (a, b) ∈ pathEdges ∧
        x (Fin.castAdd 3 a) = true ∧ x (Fin.natAdd 3 b) = true) = pathFun x := by
    decide +kernel
  intro x
  exact (hF x).trans (h x)

lemma path_size_lower (C : Circuit) (hC : IsAO2 6 C)
    (hF : computesPath C) (hs : servedPath C) : 8 ≤ C.size := by
  have ha := path_and_count_nat C hC (path_computes_explicit C hF)
  have ho := path_or_count C hC hF hs
  have hc := gate_count_partition C hC
  change 8 ≤ C.gates.length
  omega

end H5Rectangles

namespace H5DirtyControl

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : Finset (Fin 3 × Fin 3) := {(0, 0), (1, 0), (1, 1), (2, 1), (2, 2)}

def circuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [2, 5]⟩,
    ⟨.or, [4, 9]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [4, 5]⟩], 12⟩

lemma no_four : ∀ (a a' : Fin 3) (b b' : Fin 3), a ≠ a' → b ≠ b' →
    ¬ ((a, b) ∈ edges ∧ (a, b') ∈ edges ∧ (a', b) ∈ edges ∧ (a', b') ∈ edges) := by
  decide +kernel

lemma ao2 : PEqualNP.TopForm.IsAO2 6 circuit := by
  decide +kernel

lemma computes : ∀ x : Fin 6 → Bool, circuitFun 6 circuit x =
    decide (∃ (a : Fin 3) (b : Fin 3), (a, b) ∈ edges ∧
      x (Fin.castAdd 3 a) = true ∧ x (Fin.natAdd 3 b) = true) := by
  decide +kernel

lemma no_mixed_or : PEqualNP.TwoColour.tCount 6 circuit (fun i => decide (3 ≤ i)) = 0 := by
  decide +kernel

lemma pure_zero : ∀ x : Fin 6 → Bool,
    (circuit.wires (List.ofFn x)).getD 6 false =
      decide (∃ a ∈ ({0, 1} : Finset (Fin 3)), x (Fin.castAdd 3 a) = true) := by
  decide +kernel

lemma pure_two : ∀ x : Fin 6 → Bool,
    (circuit.wires (List.ofFn x)).getD 8 false =
      decide (∃ a ∈ ({1, 2} : Finset (Fin 3)), x (Fin.castAdd 3 a) = true) := by
  decide +kernel

lemma pure_seven : ∀ x : Fin 6 → Bool,
    (circuit.wires (List.ofFn x)).getD 13 false =
      decide (∃ b ∈ ({1, 2} : Finset (Fin 3)), x (Fin.natAdd 3 b) = true) := by
  decide +kernel

lemma served : ∀ (a : Fin 3) (b : Fin 3), (a, b) ∈ edges →
    (∃ (j : ℕ) (Q : Finset (Fin 3)), j < circuit.gates.length ∧
      (NestedCover.gateAt circuit j).op = GateOp.or ∧ 2 ≤ Q.card ∧ b ∈ Q ∧
      (∀ b' ∈ Q, (a, b') ∈ edges) ∧ ∀ x : Fin 6 → Bool,
        (circuit.wires (List.ofFn x)).getD (6 + j) false =
          decide (∃ b' ∈ Q, x (Fin.natAdd 3 b') = true)) ∨
    (∃ (j : ℕ) (P : Finset (Fin 3)), j < circuit.gates.length ∧
      (NestedCover.gateAt circuit j).op = GateOp.or ∧ 2 ≤ P.card ∧ a ∈ P ∧
      (∀ a' ∈ P, (a', b) ∈ edges) ∧ ∀ x : Fin 6 → Bool,
        (circuit.wires (List.ofFn x)).getD (6 + j) false =
          decide (∃ a' ∈ P, x (Fin.castAdd 3 a') = true)) := by
  intro a b hab
  fin_cases a <;> fin_cases b
  · right
    exact ⟨0, {0, 1}, by decide +kernel, rfl, by decide +kernel,
      by decide +kernel, by decide +kernel, pure_zero⟩
  · simp [edges] at hab
  · simp [edges] at hab
  · right
    exact ⟨0, {0, 1}, by decide +kernel, rfl, by decide +kernel,
      by decide +kernel, by decide +kernel, pure_zero⟩
  · right
    exact ⟨2, {1, 2}, by decide +kernel, rfl, by decide +kernel,
      by decide +kernel, by decide +kernel, pure_two⟩
  · simp [edges] at hab
  · simp [edges] at hab
  · right
    exact ⟨2, {1, 2}, by decide +kernel, rfl, by decide +kernel,
      by decide +kernel, by decide +kernel, pure_two⟩
  · left
    exact ⟨7, {1, 2}, by decide +kernel, rfl, by decide +kernel,
      by decide +kernel, by decide +kernel, pure_seven⟩

lemma wire_ten_singletons : ∀ i : Fin 6,
    (circuit.wires (List.ofFn (fun k : Fin 6 => decide (k = i)))).getD 10 false =
      decide (i = 4) := by
  decide +kernel

lemma wire_ten_not_pure : ¬ ∃ Q : Finset (Fin 6), ∀ x : Fin 6 → Bool,
    (circuit.wires (List.ofFn x)).getD 10 false =
      decide (∃ i ∈ Q, x i = true) := by
  rintro ⟨Q, hQ⟩
  have hsub : ∀ i ∈ Q, i = (4 : Fin 6) := by
    intro i hi
    have h := hQ (fun k => decide (k = i))
    rw [wire_ten_singletons] at h
    have : decide (i = (4 : Fin 6)) = true := by
      rw [h]
      exact decide_eq_true ⟨i, hi, by simp⟩
    exact of_decide_eq_true this
  let x : Fin 6 → Bool := fun i => decide (i = 2 ∨ i = 5)
  have hx : (circuit.wires (List.ofFn x)).getD 10 false = true := by
    decide +kernel
  have hz : decide (∃ i ∈ Q, x i = true) = false := by
    apply decide_eq_false
    rintro ⟨i, hi, hxi⟩
    have := hsub i hi
    subst i
    simp [x] at hxi
  have h := hQ x
  rw [hx, hz] at h
  contradiction

lemma dirty_top : 5 < circuit.gates.length ∧
    (NestedCover.gateAt circuit 5).op = GateOp.and ∧
    PEqualNP.TopForm.opnd circuit 5 1 = 10 ∧
    PEqualNP.CleanedNonEdge.OrReaches 6 circuit circuit.output 5 := by
  exact ⟨by decide +kernel, rfl, rfl, by decide +kernel⟩

lemma edge_active : ∀ j : Fin circuit.gates.length,
    ∃ (a : Fin 3) (b : Fin 3), (a, b) ∈ edges ∧
      (circuit.wires (List.ofFn (fun i : Fin 6 =>
        decide (i = Fin.castAdd 3 a ∨ i = Fin.natAdd 3 b)))).getD (6 + j.val) false = true := by
  decide +kernel

lemma size_eight : circuit.size = 8 := rfl

end H5DirtyControl

namespace H5Rectangles

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.Outside.L_meta_4970_aux.H5AndCount

lemma dirty_computes_path : computesPath H5DirtyControl.circuit := H5DirtyControl.computes

lemma dirty_served_path : servedPath H5DirtyControl.circuit := H5DirtyControl.served

lemma dirty_minimum_size : ∀ C : Circuit, IsAO2 6 C → computesPath C →
    servedPath C → H5DirtyControl.circuit.size ≤ C.size := by
  intro C hC hF hs
  rw [H5DirtyControl.size_eight]
  exact path_size_lower C hC hF hs

lemma dirty_and_count : (andNatGates H5DirtyControl.circuit).card = 3 := by
  decide +kernel

lemma dirty_minimum_and : ∀ C : Circuit, IsAO2 6 C → computesPath C →
    (andNatGates H5DirtyControl.circuit).card ≤ (andNatGates C).card := by
  intro C hC hF
  rw [dirty_and_count]
  exact path_and_count_nat C hC (path_computes_explicit C hF)

end H5Rectangles

namespace H5ChargeCounter

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def edges : Finset (Fin 3 × Fin 5) := {(0,0),(0,1),(0,2),(0,3),(1,3),(1,4)}

def circuit : Circuit :=
  ⟨[⟨.or,[2,1]⟩,⟨.and,[6,8]⟩,⟨.or,[3,9]⟩,⟨.or,[4,10]⟩,⟨.or,[5,11]⟩,
    ⟨.or,[6,12]⟩,⟨.or,[6,7]⟩,⟨.and,[0,13]⟩,⟨.and,[1,14]⟩,⟨.or,[15,16]⟩],17⟩

def edgeFun (x : Fin 8 → Bool) : Bool :=
  decide (∃ (a : Fin 3) (b : Fin 5), (a,b) ∈ edges ∧
    x (Fin.castAdd 5 a) = true ∧ x (Fin.natAdd 3 b) = true)

def value (j : ℕ) (x : Fin 8 → Bool) : Bool :=
  (circuit.wires (List.ofFn x)).getD (8+j) false

def star (Q : Finset (Fin 8)) (x : Fin 8 → Bool) : Bool :=
  decide (∃ a ∈ Q, x a = true)

def single (a : Fin 8) : Fin 8 → Bool := fun b => decide (b = a)

def singletonSupport (j : ℕ) : Finset (Fin 8) :=
  Finset.univ.filter fun a => value j (single a) = true

def pureCheck (j : ℕ) : Bool :=
  decide (∀ x : Fin 8 → Bool, value j x = star (singletonSupport j) x)

def belowCheck (j : ℕ) : Bool :=
  decide (∀ x : Fin 8 → Bool, value j x = true → edgeFun x = true)

def isOr (op : GateOp) : Bool :=
  match op with
  | .or => true
  | _ => false

def isAnd (op : GateOp) : Bool :=
  match op with
  | .and => true
  | _ => false

def charged : Finset (Fin 10) :=
  Finset.univ.filter fun j => isOr (gateAt circuit j.val).op && (pureCheck j.val || belowCheck j.val)

lemma no_four : ∀ (a a' : Fin 3) (b b' : Fin 5), a ≠ a' → b ≠ b' →
    ¬ ((a,b) ∈ edges ∧ (a,b') ∈ edges ∧ (a',b) ∈ edges ∧ (a',b') ∈ edges) := by
  decide +kernel

lemma ao2 : PEqualNP.TopForm.IsAO2 8 circuit := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma computes : ∀ x : Fin 8 → Bool, circuitFun 8 circuit x = edgeFun x := by
  decide +kernel

lemma no_mixed_or : PEqualNP.TwoColour.tCount 8 circuit (fun i => decide (3 ≤ i)) = 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma pure_r : ∀ x : Fin 8 → Bool, value 0 x =
    decide (∃ a ∈ ({1,2} : Finset (Fin 3)), x (Fin.castAdd 5 a) = true) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma pure_Q : ∀ x : Fin 8 → Bool, value 5 x =
    decide (∃ b ∈ ({0,1,2,3} : Finset (Fin 5)), x (Fin.natAdd 3 b) = true) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma pure_R : ∀ x : Fin 8 → Bool, value 6 x =
    decide (∃ b ∈ ({3,4} : Finset (Fin 5)), x (Fin.natAdd 3 b) = true) := by
  decide +kernel

lemma served : ∀ (a : Fin 3) (b : Fin 5), (a,b) ∈ edges →
    (∃ (j : ℕ) (Q : Finset (Fin 5)), j < circuit.gates.length ∧
      (gateAt circuit j).op = .or ∧ 2 ≤ Q.card ∧ b ∈ Q ∧
      (∀ b' ∈ Q, (a,b') ∈ edges) ∧ ∀ x : Fin 8 → Bool,
        value j x = decide (∃ b' ∈ Q, x (Fin.natAdd 3 b') = true)) ∨
    (∃ (j : ℕ) (P : Finset (Fin 3)), j < circuit.gates.length ∧
      (gateAt circuit j).op = .or ∧ 2 ≤ P.card ∧ a ∈ P ∧
      (∀ a' ∈ P, (a',b) ∈ edges) ∧ ∀ x : Fin 8 → Bool,
        value j x = decide (∃ a' ∈ P, x (Fin.castAdd 5 a') = true)) := by
  intro a b hab
  have hcases : (a = 0 ∧ b ∈ ({0,1,2,3} : Finset (Fin 5))) ∨
      (a = 1 ∧ b ∈ ({3,4} : Finset (Fin 5))) := by
    fin_cases a <;> fin_cases b <;> simp_all [edges]
  rcases hcases with ⟨rfl,hb⟩ | ⟨rfl,hb⟩
  · left
    exact ⟨5,{0,1,2,3},by decide +kernel,rfl,by decide +kernel,hb,
      by decide +kernel,pure_Q⟩
  · left
    exact ⟨6,{3,4},by decide +kernel,rfl,by decide +kernel,hb,
      by decide +kernel,pure_R⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_active : ∀ j : Fin circuit.gates.length,
    ∃ (a : Fin 3) (b : Fin 5), (a,b) ∈ edges ∧
      value j.val (fun i => decide (i = Fin.castAdd 5 a ∨ i = Fin.natAdd 3 b)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma checks : ∀ j : Fin 10,
    (pureCheck j.val = true ↔ j = 0 ∨ j = 5 ∨ j = 6) ∧
    (belowCheck j.val = true ↔ j = 7 ∨ j = 8 ∨ j = 9) := by
  decide +kernel

lemma pureCheck_iff (j : ℕ) : pureCheck j = true ↔
    ∃ Q : Finset (Fin 8), ∀ x : Fin 8 → Bool, value j x = star Q x := by
  rw [pureCheck, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨singletonSupport j,h⟩
  · rintro ⟨Q,hQ⟩
    have he : singletonSupport j = Q := by
      ext a
      simp only [singletonSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hQ]
      simp [star,single]
    rw [he]
    exact hQ

lemma normal_form : ∀ i < circuit.gates.length, ∀ j < circuit.gates.length,
    (gateAt circuit i).op = .and →
    (∀ x : Fin 8 → Bool, value i x = true → edgeFun x = true) →
    (gateAt circuit j).op = .and → ¬ PEqualNP.EdgeOwnership.InCone 8 circuit i j := by
  have hc : ∀ i j : Fin 10, isAnd (gateAt circuit i.val).op = true →
      (i = 7 ∨ i = 8 ∨ i = 9) → isAnd (gateAt circuit j.val).op = true →
      ¬ PEqualNP.EdgeOwnership.InCone 8 circuit i.val j.val := by
    decide +kernel
  intro i hi j hj hiAnd hBelow hjAnd
  have hi' : i < 10 := hi
  have hj' : j < 10 := hj
  have hcheck : belowCheck i = true := decide_eq_true hBelow
  exact hc ⟨i,hi'⟩ ⟨j,hj'⟩ (by rw [hiAnd]; rfl)
    ((checks ⟨i,hi'⟩).2.mp hcheck) (by rw [hjAnd]; rfl)

lemma charged_eq : charged = {0,5,6,9} := by
  ext j
  simp only [charged,Finset.mem_filter,Finset.mem_univ,true_and,Bool.and_eq_true,Bool.or_eq_true]
  rw [(checks j).1, (checks j).2]
  fin_cases j <;> decide +kernel

lemma charged_card : charged.card = 4 := by
  rw [charged_eq]
  decide +kernel

lemma charge_bound_fails : charged.card + 1 < edges.card := by
  rw [charged_card]
  decide +kernel

lemma size_ten : circuit.size = 10 := rfl

def pureLeft (j : ℕ) : Prop := ∃ Q : Finset (Fin 3), 2 ≤ Q.card ∧
  ∀ x : Fin 8 → Bool, value j x = decide (∃ a ∈ Q, x (Fin.castAdd 5 a) = true)

def pureRight (j : ℕ) : Prop := ∃ Q : Finset (Fin 5), 2 ≤ Q.card ∧
  ∀ x : Fin 8 → Bool, value j x = decide (∃ b ∈ Q, x (Fin.natAdd 3 b) = true)

lemma pure_palette_iff (j : Fin 10) : pureLeft j.val ∨ pureRight j.val ↔ pureCheck j.val = true := by
  constructor
  · intro h
    apply (pureCheck_iff j.val).mpr
    rcases h with ⟨Q,hcard,hQ⟩ | ⟨Q,hcard,hQ⟩
    · refine ⟨Q.image (Fin.castAdd 5), ?_⟩
      intro x
      rw [hQ x]
      apply Bool.eq_iff_iff.mpr
      simp [star]
    · refine ⟨Q.image (Fin.natAdd 3), ?_⟩
      intro x
      rw [hQ x]
      apply Bool.eq_iff_iff.mpr
      simp [star]
  · intro h
    rcases (checks j).1.mp h with rfl | rfl | rfl
    · exact Or.inl ⟨{1,2},by decide +kernel,pure_r⟩
    · exact Or.inr ⟨{0,1,2,3},by decide +kernel,pure_Q⟩
    · exact Or.inr ⟨{3,4},by decide +kernel,pure_R⟩

noncomputable def paletteCharged : Finset (Fin 10) := by
  classical
  exact Finset.univ.filter fun j => (gateAt circuit j.val).op = .or ∧
    ((pureLeft j.val ∨ pureRight j.val) ∨
      ∀ x : Fin 8 → Bool, value j.val x = true → edgeFun x = true)

lemma isOr_true_iff (op : GateOp) : isOr op = true ↔ op = .or := by
  cases op <;> simp [isOr]

lemma paletteCharged_eq : paletteCharged = charged := by
  ext j
  simp only [paletteCharged,charged,Finset.mem_filter,Finset.mem_univ,true_and,
    Bool.and_eq_true,Bool.or_eq_true,isOr_true_iff]
  rw [pure_palette_iff j, belowCheck, decide_eq_true_eq]

lemma exact_palette_charge_fails : paletteCharged.card = 4 ∧ paletteCharged.card + 1 < edges.card := by
  rw [paletteCharged_eq]
  exact ⟨charged_card,charge_bound_fails⟩

def incidence (u v : Fin 8) : Prop :=
  ∃ (a : Fin 3) (b : Fin 5), (a,b) ∈ edges ∧ u = Fin.castAdd 5 a ∧ v = Fin.natAdd 3 b

def graph : SimpleGraph (Fin 8) := SimpleGraph.fromRel incidence

abbrev graphDec : DecidableRel graph.Adj := by
  intro u v
  change Decidable (u ≠ v ∧ (incidence u v ∨ incidence v u))
  unfold incidence
  infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma graph_computes : ∀ x : Fin 8 → Bool,
    @graphFun 8 graph graphDec ∅ x = edgeFun x := by
  decide +kernel

lemma graph_no_four : @PEqualNP.TopForm.NoFourCycle 8 graph graphDec := by
  decide +kernel

lemma top_form : @PEqualNP.TopForm.TopForm 8 graph graphDec circuit := by
  intro i hi j hj hiAnd hBelow hjAnd
  apply normal_form i hi j hj hiAnd _ hjAnd
  intro x hx
  have h := hBelow x hx
  rw [graph_computes x] at h
  exact h

end H5ChargeCounter

namespace H5DifferenceTrace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm H5Pruning

lemma difference_trace (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (x z : Fin n → Bool) (b : Fin n)
    (hdiff : ∀ a, x a = true → z a = false → a = b) (w : ℕ)
    (hx : wireFn n C w x = true) (hz : wireFn n C w z = false) :
    b ∈ orIn n C w ∨
      ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
        ∃ v ∈ (gateAt C j).inputs,
          b ∈ orIn n C v ∧ wireFn n C v x = true ∧ wireFn n C v z = false := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hin : w < n
    · have hxb := hx
      have hzb := hz
      rw [wireFn_input n C w hin] at hxb hzb
      have he := hdiff ⟨w, hin⟩ hxb hzb
      left
      rw [H5Reach.orIn_input n C w hin]
      exact Finset.mem_singleton.mpr he.symm
    · have hvalid : w < n + C.gates.length := by
        by_contra h
        rw [wireFn_ge n C w (by omega)] at hx
        cases hx
      let j := w - n
      have hj : j < C.gates.length := by omega
      have hw : n + j = w := by omega
      obtain ⟨u, v, hu, hv, hinp, hop, hval⟩ := binary_gate n C hC j hj
      have hex := hval x
      have hez := hval z
      rw [hw, hx] at hex
      rw [hw, hz] at hez
      rcases hop with hop | hop
      · have hxx : wireFn n C u x = true ∧ wireFn n C v x = true := by
          simpa [hop, GateOp.eval] using hex.symm
        have hzz : wireFn n C u z = false ∨ wireFn n C v z = false := by
          cases huz : wireFn n C u z with
          | false => exact Or.inl rfl
          | true =>
              right
              simpa [hop, GateOp.eval, huz] using hez.symm
        rcases hzz with hzu | hzv
        · rcases ih u (by omega) hxx.1 hzu with hr | hr
          · exact Or.inr ⟨j, hj, hop, u, by simp [hinp], hr, hxx.1, hzu⟩
          · exact Or.inr hr
        · rcases ih v (by omega) hxx.2 hzv with hr | hr
          · exact Or.inr ⟨j, hj, hop, v, by simp [hinp], hr, hxx.2, hzv⟩
          · exact Or.inr hr
      · have hxx : wireFn n C u x = true ∨ wireFn n C v x = true := by
          simpa [hop, GateOp.eval] using hex.symm
        have hzz : wireFn n C u z = false ∧ wireFn n C v z = false := by
          simpa [hop, GateOp.eval] using hez.symm
        rcases hxx with hxu | hxv
        · rcases ih u (by omega) hxu hzz.1 with hr | hr
          · left
            rw [← hw]
            exact H5Reach.orIn_up n C j u b hj hop (by simp [hinp]) hu hr
          · exact Or.inr hr
        · rcases ih v (by omega) hxv hzz.2 with hr | hr
          · left
            rw [← hw]
            exact H5Reach.orIn_up n C j v b hj hop (by simp [hinp]) hv hr
          · exact Or.inr hr

lemma difference_trace_and (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (x z : Fin n → Bool) (b : Fin n)
    (hdiff : ∀ a, x a = true → z a = false → a = b) (w : ℕ)
    (hx : wireFn n C w x = true) (hz : wireFn n C w z = false)
    (hnoreach : b ∉ orIn n C w) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      ∃ v ∈ (gateAt C j).inputs,
        b ∈ orIn n C v ∧ wireFn n C v x = true ∧ wireFn n C v z = false := by
  exact (difference_trace n C hC x z b hdiff w hx hz).resolve_left hnoreach

lemma difference_trace_and_of_singleton_false (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (x z : Fin n → Bool) (b : Fin n)
    (hdiff : ∀ a, x a = true → z a = false → a = b) (w : ℕ)
    (hx : wireFn n C w x = true) (hz : wireFn n C w z = false)
    (hsingle : wireFn n C w (singletonInput b) = false) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      ∃ v ∈ (gateAt C j).inputs,
        b ∈ orIn n C v ∧ wireFn n C v x = true ∧ wireFn n C v z = false := by
  apply difference_trace_and n C hC x z b hdiff w hx hz
  intro hr
  have ht := H5LiftGlue.orIn_singleton_true n C hC.2.1 w b hr
  rw [hsingle] at ht
  cases ht

lemma orIn_false (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (z : Fin n → Bool) (w : ℕ) (hz : wireFn n C w z = false)
    (a : Fin n) (ha : a ∈ orIn n C w) : z a = false := by
  cases hza : z a with
  | false => rfl
  | true =>
      have hle : singletonInput a ≤ z := by
        intro c
        apply Bool.le_iff_imp.mpr
        intro hc
        have hca : c = a := by simpa [singletonInput] using hc
        simpa [hca] using hza
      have htrue := H5LiftGlue.orIn_singleton_true n C hC.2.1 w a ha
      have ht := Bool.le_iff_imp.mp (wireFn_mono n C hC w hle) htrue
      rw [hz] at ht
      cases ht

lemma difference_trace_confined (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (x z : Fin n → Bool) (b : Fin n)
    (hdiff : ∀ a, x a = true → z a = false → a = b) (w : ℕ)
    (hx : wireFn n C w x = true) (hz : wireFn n C w z = false)
    (hsingle : wireFn n C w (singletonInput b) = false) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      ∃ v ∈ (gateAt C j).inputs,
        b ∈ orIn n C v ∧ wireFn n C v x = true ∧ wireFn n C v z = false ∧
          ∀ a ∈ orIn n C v, z a = false := by
  obtain ⟨j, hj, hop, v, hv, hb, hvx, hvz⟩ :=
    difference_trace_and_of_singleton_false n C hC x z b hdiff w hx hz hsingle
  exact ⟨j, hj, hop, v, hv, hb, hvx, hvz, orIn_false n C hC z v hvz⟩

end H5DifferenceTrace

namespace H5AndReplace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour
open H5Pruning H5Bridge H5Reach

def replace (C : Circuit) (j i : ℕ) : Circuit :=
  ⟨C.gates.take j ++ ⟨GateOp.and, [i,i]⟩ :: C.gates.drop (j+1), C.output⟩

lemma replace_gates_set (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (i : ℕ) :
    (replace C j i).gates = C.gates.set j ⟨.and,[i,i]⟩ :=
  take_cons_drop_set C.gates j _ hj

lemma replace_length (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (i : ℕ) :
    (replace C j i).gates.length = C.gates.length := by
  rw [replace_gates_set C j hj i]
  exact List.length_set

lemma replace_gateAt_self (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (i : ℕ) :
    gateAt (replace C j i) j = ⟨.and,[i,i]⟩ := by
  unfold gateAt
  rw [replace_gates_set C j hj i]
  simp [hj]

lemma replace_gateAt_other (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (i k : ℕ) (hk : k ≠ j) : gateAt (replace C j i) k = gateAt C k := by
  unfold gateAt
  rw [replace_gates_set C j hj i]
  by_cases hkl : k < C.gates.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hkl), List.getD_eq_getElem _ _ hkl]
    exact List.getElem_set_ne (Ne.symm hk) _
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hkl),
      List.getD_eq_default _ _ (Nat.le_of_not_lt hkl)]

lemma replace_gateAt_op (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (i : ℕ)
    (hop : (gateAt C j).op = .and) (k : ℕ) :
    (gateAt (replace C j i) k).op = (gateAt C k).op := by
  by_cases hk : k = j
  · subst k
    rw [replace_gateAt_self C j hj i]
    exact hop.symm
  · rw [replace_gateAt_other C j hj i k hk]

lemma replace_good (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (i : ℕ) (hi : i < n+j)
    (_hop : (gateAt C j).op = .and) : IsAO2 n (replace C j i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [replace, List.mem_append, List.mem_cons] at hg
    rcases hg with hg | rfl | hg
    · exact hC.1 g (List.mem_of_mem_take hg)
    · exact Or.inl rfl
    · exact hC.1 g (List.mem_of_mem_drop hg)
  · intro k hk w hw
    have hk' : k < C.gates.length := by simpa [replace_length C j hj i] using hk
    by_cases hkj : k = j
    · subst k
      rw [replace_gateAt_self C j hj i] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hw
      subst w
      exact hi
    · rw [replace_gateAt_other C j hj i k hkj] at hw
      exact hC.2.1 k hk' w hw
  · intro g hg
    simp only [replace, List.mem_append, List.mem_cons] at hg
    rcases hg with hg | rfl | hg
    · exact hC.2.2 g (List.mem_of_mem_take hg)
    · rfl
    · exact hC.2.2 g (List.mem_of_mem_drop hg)

lemma replace_size (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (i : ℕ) :
    (replace C j i).size = C.size := replace_length C j hj i

lemma replace_indexed_andCount (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (i : ℕ)
    (hop : (gateAt C j).op = .and) :
    H5OrLift.andCount (replace C j i) = H5OrLift.andCount C := by
  unfold H5OrLift.andCount
  rw [replace_length C j hj i]
  congr 1
  apply Finset.filter_congr
  intro k hk
  rw [replace_gateAt_op C j hj i hop k]

lemma replace_andCount (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (i : ℕ)
    (hop : (gateAt C j).op = .and) :
    H5Count.andCount (replace C j i).gates = H5Count.andCount C.gates := by
  rw [← H5Count.indexed_andCount_eq, ← H5Count.indexed_andCount_eq]
  exact replace_indexed_andCount C j hj i hop

lemma replace_andIndexSum (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (i : ℕ)
    (hop : (gateAt C j).op = .and) :
    H5OrLift.andIndexSum (replace C j i) = H5OrLift.andIndexSum C := by
  unfold H5OrLift.andIndexSum
  rw [replace_length C j hj i]
  congr 1
  apply Finset.filter_congr
  intro k hk
  rw [replace_gateAt_op C j hj i hop k]

lemma replace_reachValues (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (i : ℕ) (hop : (gateAt C j).op = .and) :
    reachValues n (replace C j i).gates = reachValues n C.gates := by
  classical
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j+1) := by
    have h := (List.take_append_drop j C.gates).symm
    rw [List.drop_eq_getElem_cons hj] at h
    exact h
  have hop' : (C.gates[j]).op = .and := by simpa [gateAt, hj] using hop
  unfold reachValues
  change reachFrom (C.gates.take j ++ ⟨.and,[i,i]⟩ :: C.gates.drop (j+1)) _ = _
  conv_rhs => rw [hsplit]
  rw [reachFrom_append, reachFrom_append]
  simp only [reachFrom, List.foldl_cons, hop', reduceCtorEq, ↓reduceIte]

lemma replace_orIn (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (i : ℕ) (hi : i < n+j)
    (hop : (gateAt C j).op = .and) (w : ℕ) :
    orIn n (replace C j i) w = orIn n C w := by
  rw [← reachValues_eq_orIn n (replace C j i) (replace_good n C hC j hj i hi hop).2.1 w,
    ← reachValues_eq_orIn n C hC.2.1 w, replace_reachValues n C j hj i hop]

lemma replace_tCount (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (i : ℕ) (hi : i < n+j)
    (hop : (gateAt C j).op = .and) (lin : ℕ → Bool) :
    tCount n (replace C j i) lin = tCount n C lin := by
  unfold tCount twoColour
  rw [replace_length C j hj i]
  congr 1
  apply Finset.filter_congr
  intro k hk
  unfold IsTwoColour
  rw [replace_length C j hj i, replace_gateAt_op C j hj i hop k,
    replace_orIn n C hC j hj i hi hop (n+k)]

end H5AndReplace


namespace H5AndReplace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open H5Pruning H5Bridge H5Stars

lemma prefix_value (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (i : ℕ) (hi : i < n+j) (x : Fin n → Bool) :
    (wiresFrom (C.gates.take j) (List.ofFn x)).getD i false = wireFn n C i x := by
  rw [getD_wiresFrom_take C.gates (List.ofFn x) j i (Nat.le_of_lt hj)]
  simp only [List.length_ofFn, hi, ↓reduceIte]
  rfl

lemma original_wires_split (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    C.wires (List.ofFn x) = wiresFrom (C.gates.drop (j+1))
      (wiresFrom (C.gates.take j) (List.ofFn x) ++ [wireFn n C (n+j) x]) := by
  let pre := wiresFrom (C.gates.take j) (List.ofFn x)
  let v := (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun k => pre.getD k false)
  have hlen : pre.length = n+j := by
    simp [pre, length_wiresFrom, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hsplit : C.wires (List.ofFn x) = wiresFrom (C.gates.drop (j+1)) (pre ++ [v]) :=
    wires_split C j hj _
  have hv : wireFn n C (n+j) x = v := by
    unfold wireFn
    rw [hsplit, getD_wiresFrom_lt]
    · simp [← hlen]
    · simp [hlen]
  simpa [hv] using hsplit

lemma replace_wires (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (i : ℕ) (hi : i < n+j) (x : Fin n → Bool) :
    (replace C j i).wires (List.ofFn x) = wiresFrom (C.gates.drop (j+1))
      (wiresFrom (C.gates.take j) (List.ofFn x) ++ [wireFn n C i x]) := by
  change wiresFrom (C.gates.take j ++ ⟨GateOp.and, [i,i]⟩ :: C.gates.drop (j+1)) (List.ofFn x) = _
  rw [wiresFrom_append]
  change wiresFrom (C.gates.drop (j+1))
      (wiresFrom (C.gates.take j) (List.ofFn x) ++
        [GateOp.and.eval ([i,i].map fun k => (wiresFrom (C.gates.take j) (List.ofFn x)).getD k false)]) = _
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
    id_eq, Bool.and_true, Bool.and_self]
  rw [prefix_value n C j hj i hi x]

lemma replace_wire_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (i : ℕ) (hi : i < n+j) (x : Fin n → Bool) :
    wireFn n (replace C j i) (n+j) x = wireFn n C i x := by
  unfold wireFn
  rw [replace_wires n C j hj i hi x, getD_wiresFrom_lt]
  · have hlen : (wiresFrom (C.gates.take j) (List.ofFn x)).length = n+j := by
      simp [length_wiresFrom, Nat.min_eq_left (Nat.le_of_lt hj)]
    rw [← hlen, getD_snoc_eq]
    rfl
  · simp [length_wiresFrom, Nat.min_eq_left (Nat.le_of_lt hj)]

lemma replace_wire_prefix (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (i : ℕ) (hi : i < n+j) (w : ℕ) (hw : w < n+j) (x : Fin n → Bool) :
    wireFn n (replace C j i) w x = wireFn n C w x := by
  unfold wireFn
  rw [replace_wires n C j hj i hi x, getD_wiresFrom_lt]
  · rw [List.getD_append]
    · exact prefix_value n C j hj w hw x
    · simp [length_wiresFrom, Nat.min_eq_left (Nat.le_of_lt hj), hw]
  · simp [length_wiresFrom, Nat.min_eq_left (Nat.le_of_lt hj)]
    omega

lemma replace_wires_eq (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (i : ℕ) (hi : i < n+j) (x : Fin n → Bool)
    (heq : wireFn n C i x = wireFn n C (n+j) x) :
    (replace C j i).wires (List.ofFn x) = C.wires (List.ofFn x) := by
  rw [replace_wires n C j hj i hi x, original_wires_split n C j hj x, heq]

lemma replace_wire_eq (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (i : ℕ) (hi : i < n+j) (x : Fin n → Bool)
    (heq : wireFn n C i x = wireFn n C (n+j) x) (w : ℕ) :
    wireFn n (replace C j i) w x = wireFn n C w x := by
  unfold wireFn
  rw [replace_wires_eq n C j hj i hi x heq]

lemma replace_andOr (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (j i : ℕ) :
    ∀ g ∈ (replace C j i).gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  simp only [replace, List.mem_append, List.mem_cons] at hg
  rcases hg with hg | rfl | hg
  · exact hC.1 g (List.mem_of_mem_take hg)
  · exact Or.inl rfl
  · exact hC.1 g (List.mem_of_mem_drop hg)

lemma replace_wire_mono (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (j i w : ℕ) :
    Monotone (wireFn n (replace C j i) w) :=
  wireFn_mono_of_andOr n _ (replace_andOr n C hC j i) w

lemma replace_wire_le_at (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (i : ℕ) (hi : i < n+j)
    (x : Fin n → Bool) (hle : wireFn n C i x ≤ wireFn n C (n+j) x) (w : ℕ) :
    wireFn n (replace C j i) w x ≤ wireFn n C w x := by
  apply Bool.le_iff_imp.mpr
  unfold wireFn
  rw [replace_wires n C j hj i hi x, original_wires_split n C j hj x]
  apply wiresFrom_mono (C.gates.drop (j+1))
    (fun g hg => hC.1 g (List.mem_of_mem_drop hg)) _ _ (by simp)
  intro k hk
  let pre := wiresFrom (C.gates.take j) (List.ofFn x)
  change (pre ++ [wireFn n C i x]).getD k false = true at hk
  change (pre ++ [wireFn n C (n+j) x]).getD k false = true
  by_cases hklt : k < pre.length
  · rw [List.getD_append _ _ _ _ hklt] at hk
    rw [List.getD_append _ _ _ _ hklt]
    exact hk
  · by_cases hkeq : k = pre.length
    · subst k
      rw [getD_snoc_eq] at hk
      rw [getD_snoc_eq]
      exact Bool.le_iff_imp.mp hle hk
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hk
      cases hk

lemma replace_wire_le (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (i : ℕ) (hi : i < n+j)
    (hle : ∀ x, wireFn n C i x ≤ wireFn n C (n+j) x) :
    ∀ w x, wireFn n (replace C j i) w x ≤ wireFn n C w x := by
  intro w x
  exact replace_wire_le_at n C hC j hj i hi x (hle x) w

lemma replace_graph_preserved (n : ℕ) (E : Finset (Fin n × Fin n))
    (C : Circuit) (hC : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (i : ℕ) (hi : i < n+j)
    (hle : ∀ x, wireFn n C i x ≤ wireFn n C (n+j) x)
    (heq : ∀ e ∈ E, wireFn n C i (pairInput e.1 e.2) =
      wireFn n C (n+j) (pairInput e.1 e.2))
    (w : ℕ) (hspec : ∀ x, wireFn n C w x = H5Pruning.graphFun E x) :
    ∀ x, wireFn n (replace C j i) w x = H5Pruning.graphFun E x := by
  apply H5Essential.graph_eq_of_positive_and_le n E _ (replace_wire_mono n C hC j i w)
  · intro x
    rw [← hspec x]
    exact replace_wire_le_at n C hC j hj i hi x (hle x) w
  · intro e he
    rw [replace_wire_eq n C j hj i hi _ (heq e he) w, hspec]
    apply decide_eq_true
    exact ⟨e,he,by simp [pairInput],by simp [pairInput]⟩

lemma replace_star_preserved (n : ℕ) (Q : Finset (Fin n))
    (C : Circuit) (hC : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (i : ℕ) (hi : i < n+j)
    (hle : ∀ x, wireFn n C i x ≤ wireFn n C (n+j) x)
    (heq : ∀ u ∈ Q, wireFn n C i (singletonInput u) =
      wireFn n C (n+j) (singletonInput u))
    (w : ℕ) (hstar : ∀ x, wireFn n C w x = starFun Q x) :
    ∀ x, wireFn n (replace C j i) w x = starFun Q x := by
  intro x
  cases hx : starFun Q x with
  | false =>
      have h := replace_wire_le_at n C hC j hj i hi x (hle x) w
      rw [hstar, hx] at h
      exact le_antisymm h (by cases wireFn n (replace C j i) w x <;> decide)
  | true =>
      obtain ⟨u,hu,hux⟩ := (of_decide_eq_true hx : ∃ u ∈ Q, x u = true)
      have hsingle : wireFn n C w (singletonInput u) = true := by
        rw [hstar]
        apply decide_eq_true
        exact ⟨u,hu,by simp [singletonInput]⟩
      have hnew : wireFn n (replace C j i) w (singletonInput u) = true := by
        rw [replace_wire_eq n C j hj i hi _ (heq u hu) w]
        exact hsingle
      exact Bool.le_iff_imp.mp (replace_wire_mono n C hC j i w (singletonInput_le u x hux)) hnew

lemma replace_keepsStars (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (i : ℕ) (hi : i < n+j)
    (hle : ∀ x, wireFn n C i x ≤ wireFn n C (n+j) x)
    (heq : ∀ u : Fin n, wireFn n C i (singletonInput u) =
      wireFn n C (n+j) (singletonInput u)) : KeepsStars n C (replace C j i) := by
  intro Q w hQ hstar
  exact ⟨w, replace_star_preserved n Q C hC j hj i hi hle (fun u _ => heq u) w hstar⟩

end H5AndReplace

namespace H5AndReplace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.TwoColour H5Pruning H5Bridge H5Stars

lemma replace_admissible {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : admissible p l E C)
    (j : ℕ) (hj : j < C.gates.length) (i : ℕ) (hi : i < p+l+j)
    (hop : (gateAt C j).op = .and)
    (hle : ∀ x, wireFn (p+l) C i x ≤ wireFn (p+l) C (p+l+j) x)
    (hedge : ∀ a b, (a,b) ∈ E →
      wireFn (p+l) C i (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) =
      wireFn (p+l) C (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)))
    (hsingle : ∀ u : Fin (p+l), wireFn (p+l) C i (singletonInput u) =
      wireFn (p+l) C (p+l+j) (singletonInput u)) :
    admissible p l E (replace C j i) := by
  have hspec : ∀ x, wireFn (p+l) C C.output x = H5Pruning.graphFun (bipartiteEdges E) x := by
    intro x
    rw [graphFun_bipartite]
    exact hC.2.1 x
  have hedge' : ∀ e ∈ bipartiteEdges E,
      wireFn (p+l) C i (pairInput e.1 e.2) = wireFn (p+l) C (p+l+j) (pairInput e.1 e.2) := by
    intro e he
    obtain ⟨ab,hab,rfl⟩ := Finset.mem_image.mp he
    exact hedge ab.1 ab.2 hab
  apply admissible_of_keeps E C (replace C j i) hC (replace_good (p+l) C hC.1 j hj i hi hop)
  · intro x
    change wireFn (p+l) (replace C j i) C.output x = wireFn (p+l) C C.output x
    rw [replace_graph_preserved (p+l) (bipartiteEdges E) C hC.1 j hj i hi hle hedge' C.output hspec x,
      hspec x]
  · rw [replace_tCount (p+l) C hC.1 j hj i hi hop]
    exact hC.2.2.1
  · exact replace_keepsStars (p+l) C hC.1 j hj i hi hle hsingle

end H5AndReplace


namespace H5OrReplace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour
open H5Pruning H5Bridge H5Reach

def replace (C : Circuit) (j i : ℕ) : Circuit :=
  ⟨C.gates.take j ++ ⟨GateOp.or, [i,i]⟩ :: C.gates.drop (j+1), C.output⟩

lemma replace_gates_set (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (i : ℕ) :
    (replace C j i).gates = C.gates.set j ⟨.or,[i,i]⟩ :=
  take_cons_drop_set C.gates j _ hj

lemma replace_length (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (i : ℕ) :
    (replace C j i).gates.length = C.gates.length := by
  rw [replace_gates_set C j hj i]
  exact List.length_set

lemma replace_gateAt_self (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (i : ℕ) :
    gateAt (replace C j i) j = ⟨.or,[i,i]⟩ := by
  unfold gateAt
  rw [replace_gates_set C j hj i]
  simp [hj]

lemma replace_gateAt_other (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (i k : ℕ) (hk : k ≠ j) : gateAt (replace C j i) k = gateAt C k := by
  unfold gateAt
  rw [replace_gates_set C j hj i]
  by_cases hkl : k < C.gates.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hkl), List.getD_eq_getElem _ _ hkl]
    exact List.getElem_set_ne (Ne.symm hk) _
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hkl),
      List.getD_eq_default _ _ (Nat.le_of_not_lt hkl)]

lemma replace_gateAt_op (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (i : ℕ)
    (hop : (gateAt C j).op = .or) (k : ℕ) :
    (gateAt (replace C j i) k).op = (gateAt C k).op := by
  by_cases hk : k = j
  · subst k
    rw [replace_gateAt_self C j hj i]
    exact hop.symm
  · rw [replace_gateAt_other C j hj i k hk]

lemma replace_good (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (i : ℕ) (hi : i < n+j)
    (_hop : (gateAt C j).op = .or) : IsAO2 n (replace C j i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [replace, List.mem_append, List.mem_cons] at hg
    rcases hg with hg | rfl | hg
    · exact hC.1 g (List.mem_of_mem_take hg)
    · exact Or.inr rfl
    · exact hC.1 g (List.mem_of_mem_drop hg)
  · intro k hk w hw
    have hk' : k < C.gates.length := by simpa [replace_length C j hj i] using hk
    by_cases hkj : k = j
    · subst k
      rw [replace_gateAt_self C j hj i] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hw
      subst w
      exact hi
    · rw [replace_gateAt_other C j hj i k hkj] at hw
      exact hC.2.1 k hk' w hw
  · intro g hg
    simp only [replace, List.mem_append, List.mem_cons] at hg
    rcases hg with hg | rfl | hg
    · exact hC.2.2 g (List.mem_of_mem_take hg)
    · rfl
    · exact hC.2.2 g (List.mem_of_mem_drop hg)

lemma replace_size (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (i : ℕ) :
    (replace C j i).size = C.size := replace_length C j hj i

lemma replace_indexed_andCount (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (i : ℕ)
    (hop : (gateAt C j).op = .or) :
    H5OrLift.andCount (replace C j i) = H5OrLift.andCount C := by
  unfold H5OrLift.andCount
  rw [replace_length C j hj i]
  congr 1
  apply Finset.filter_congr
  intro k hk
  rw [replace_gateAt_op C j hj i hop k]

lemma replace_andCount (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (i : ℕ)
    (hop : (gateAt C j).op = .or) :
    H5Count.andCount (replace C j i).gates = H5Count.andCount C.gates := by
  rw [← H5Count.indexed_andCount_eq, ← H5Count.indexed_andCount_eq]
  exact replace_indexed_andCount C j hj i hop

lemma replace_andIndexSum (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (i : ℕ)
    (hop : (gateAt C j).op = .or) :
    H5OrLift.andIndexSum (replace C j i) = H5OrLift.andIndexSum C := by
  unfold H5OrLift.andIndexSum
  rw [replace_length C j hj i]
  congr 1
  apply Finset.filter_congr
  intro k hk
  rw [replace_gateAt_op C j hj i hop k]

lemma replace_orIn_subset (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (i : ℕ) (hi : i < n+j)
    (hop : (gateAt C j).op = .or) (hreach : orIn n C i ⊆ orIn n C (n+j)) :
    ∀ w, orIn n (replace C j i) w ⊆ orIn n C w := by
  classical
  have hD := replace_good n C hC j hj i hi hop
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hin : w < n
    · rw [orIn_input n (replace C j i) w hin, orIn_input n C w hin]
    · by_cases hv : w < n+C.gates.length
      · let k := w-n
        have hk : k < C.gates.length := by omega
        have hkw : n+k = w := by omega
        have hkD : k < (replace C j i).gates.length := by
          rw [replace_length C j hj i]
          exact hk
        rw [← hkw]
        intro a ha
        rw [orIn_gate n (replace C j i) hD.2.1 k hkD] at ha
        by_cases hkj : k = j
        · rw [hkj] at ha ⊢
          rw [replace_gateAt_self C j hj i] at ha
          simp at ha
          exact hreach (ih i (by omega) ha)
        · rw [replace_gateAt_other C j hj i k hkj] at ha
          rw [orIn_gate n C hC.2.1 k hk]
          split_ifs with ho
          · have ha' : a ∈ (gateAt C k).inputs.toFinset.biUnion (orIn n (replace C j i)) := by
              simpa [ho] using ha
            obtain ⟨v,hv,hav⟩ := Finset.mem_biUnion.mp ha'
            apply Finset.mem_biUnion.mpr
            refine ⟨v,hv,?_⟩
            apply ih v ?_ hav
            have := hC.2.1 k hk v (List.mem_toFinset.mp hv)
            omega
          · simp [ho] at ha
      · rw [orIn_invalid n C w (by omega),
          orIn_invalid n (replace C j i) w (by rw [replace_length C j hj i]; omega)]

lemma replace_tCount_zero (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (i : ℕ) (hi : i < n+j)
    (hop : (gateAt C j).op = .or) (lin : ℕ → Bool)
    (hreach : orIn n C i ⊆ orIn n C (n+j)) (hT : tCount n C lin = 0) :
    tCount n (replace C j i) lin = 0 := by
  apply tCount_zero_of_orIn_subsets n C (replace C j i) lin hC.2.1 hT
  intro k _ _
  exact ⟨n+k, replace_orIn_subset n C hC j hj i hi hop hreach (n+k)⟩

end H5OrReplace


namespace H5OrReplace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open H5Pruning H5Bridge H5Stars

lemma prefix_value (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (i : ℕ) (hi : i < n+j) (x : Fin n → Bool) :
    (wiresFrom (C.gates.take j) (List.ofFn x)).getD i false = wireFn n C i x := by
  rw [getD_wiresFrom_take C.gates (List.ofFn x) j i (Nat.le_of_lt hj)]
  simp only [List.length_ofFn, hi, ↓reduceIte]
  rfl

lemma original_wires_split (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    C.wires (List.ofFn x) = wiresFrom (C.gates.drop (j+1))
      (wiresFrom (C.gates.take j) (List.ofFn x) ++ [wireFn n C (n+j) x]) := by
  let pre := wiresFrom (C.gates.take j) (List.ofFn x)
  let v := (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun k => pre.getD k false)
  have hlen : pre.length = n+j := by
    simp [pre, length_wiresFrom, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hsplit : C.wires (List.ofFn x) = wiresFrom (C.gates.drop (j+1)) (pre ++ [v]) :=
    wires_split C j hj _
  have hv : wireFn n C (n+j) x = v := by
    unfold wireFn
    rw [hsplit, getD_wiresFrom_lt]
    · simp [← hlen]
    · simp [hlen]
  simpa [hv] using hsplit

lemma replace_wires (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (i : ℕ) (hi : i < n+j) (x : Fin n → Bool) :
    (replace C j i).wires (List.ofFn x) = wiresFrom (C.gates.drop (j+1))
      (wiresFrom (C.gates.take j) (List.ofFn x) ++ [wireFn n C i x]) := by
  change wiresFrom (C.gates.take j ++ ⟨GateOp.or, [i,i]⟩ :: C.gates.drop (j+1)) (List.ofFn x) = _
  rw [wiresFrom_append]
  change wiresFrom (C.gates.drop (j+1))
      (wiresFrom (C.gates.take j) (List.ofFn x) ++
        [GateOp.or.eval ([i,i].map fun k => (wiresFrom (C.gates.take j) (List.ofFn x)).getD k false)]) = _
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
    id_eq, Bool.or_false, Bool.or_self]
  rw [prefix_value n C j hj i hi x]

lemma replace_wire_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (i : ℕ) (hi : i < n+j) (x : Fin n → Bool) :
    wireFn n (replace C j i) (n+j) x = wireFn n C i x := by
  unfold wireFn
  rw [replace_wires n C j hj i hi x, getD_wiresFrom_lt]
  · have hlen : (wiresFrom (C.gates.take j) (List.ofFn x)).length = n+j := by
      simp [length_wiresFrom, Nat.min_eq_left (Nat.le_of_lt hj)]
    rw [← hlen, getD_snoc_eq]
    rfl
  · simp [length_wiresFrom, Nat.min_eq_left (Nat.le_of_lt hj)]

lemma replace_wire_prefix (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (i : ℕ) (hi : i < n+j) (w : ℕ) (hw : w < n+j) (x : Fin n → Bool) :
    wireFn n (replace C j i) w x = wireFn n C w x := by
  unfold wireFn
  rw [replace_wires n C j hj i hi x, getD_wiresFrom_lt]
  · rw [List.getD_append]
    · exact prefix_value n C j hj w hw x
    · simp [length_wiresFrom, Nat.min_eq_left (Nat.le_of_lt hj), hw]
  · simp [length_wiresFrom, Nat.min_eq_left (Nat.le_of_lt hj)]
    omega

lemma replace_wires_eq (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (i : ℕ) (hi : i < n+j) (x : Fin n → Bool)
    (heq : wireFn n C i x = wireFn n C (n+j) x) :
    (replace C j i).wires (List.ofFn x) = C.wires (List.ofFn x) := by
  rw [replace_wires n C j hj i hi x, original_wires_split n C j hj x, heq]

lemma replace_wire_eq (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (i : ℕ) (hi : i < n+j) (x : Fin n → Bool)
    (heq : wireFn n C i x = wireFn n C (n+j) x) (w : ℕ) :
    wireFn n (replace C j i) w x = wireFn n C w x := by
  unfold wireFn
  rw [replace_wires_eq n C j hj i hi x heq]

lemma replace_andOr (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (j i : ℕ) :
    ∀ g ∈ (replace C j i).gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  simp only [replace, List.mem_append, List.mem_cons] at hg
  rcases hg with hg | rfl | hg
  · exact hC.1 g (List.mem_of_mem_take hg)
  · exact Or.inr rfl
  · exact hC.1 g (List.mem_of_mem_drop hg)

lemma replace_wire_mono (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (j i w : ℕ) :
    Monotone (wireFn n (replace C j i) w) :=
  wireFn_mono_of_andOr n _ (replace_andOr n C hC j i) w

lemma replace_wire_le_at (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (i : ℕ) (hi : i < n+j)
    (x : Fin n → Bool) (hle : wireFn n C i x ≤ wireFn n C (n+j) x) (w : ℕ) :
    wireFn n (replace C j i) w x ≤ wireFn n C w x := by
  apply Bool.le_iff_imp.mpr
  unfold wireFn
  rw [replace_wires n C j hj i hi x, original_wires_split n C j hj x]
  apply wiresFrom_mono (C.gates.drop (j+1))
    (fun g hg => hC.1 g (List.mem_of_mem_drop hg)) _ _ (by simp)
  intro k hk
  let pre := wiresFrom (C.gates.take j) (List.ofFn x)
  change (pre ++ [wireFn n C i x]).getD k false = true at hk
  change (pre ++ [wireFn n C (n+j) x]).getD k false = true
  by_cases hklt : k < pre.length
  · rw [List.getD_append _ _ _ _ hklt] at hk
    rw [List.getD_append _ _ _ _ hklt]
    exact hk
  · by_cases hkeq : k = pre.length
    · subst k
      rw [getD_snoc_eq] at hk
      rw [getD_snoc_eq]
      exact Bool.le_iff_imp.mp hle hk
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hk
      cases hk

lemma replace_wire_le (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (i : ℕ) (hi : i < n+j)
    (hle : ∀ x, wireFn n C i x ≤ wireFn n C (n+j) x) :
    ∀ w x, wireFn n (replace C j i) w x ≤ wireFn n C w x := by
  intro w x
  exact replace_wire_le_at n C hC j hj i hi x (hle x) w

lemma replace_graph_preserved (n : ℕ) (E : Finset (Fin n × Fin n))
    (C : Circuit) (hC : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (i : ℕ) (hi : i < n+j)
    (hle : ∀ x, wireFn n C i x ≤ wireFn n C (n+j) x)
    (heq : ∀ e ∈ E, wireFn n C i (pairInput e.1 e.2) =
      wireFn n C (n+j) (pairInput e.1 e.2))
    (w : ℕ) (hspec : ∀ x, wireFn n C w x = H5Pruning.graphFun E x) :
    ∀ x, wireFn n (replace C j i) w x = H5Pruning.graphFun E x := by
  apply H5Essential.graph_eq_of_positive_and_le n E _ (replace_wire_mono n C hC j i w)
  · intro x
    rw [← hspec x]
    exact replace_wire_le_at n C hC j hj i hi x (hle x) w
  · intro e he
    rw [replace_wire_eq n C j hj i hi _ (heq e he) w, hspec]
    apply decide_eq_true
    exact ⟨e,he,by simp [pairInput],by simp [pairInput]⟩

lemma replace_star_preserved (n : ℕ) (Q : Finset (Fin n))
    (C : Circuit) (hC : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (i : ℕ) (hi : i < n+j)
    (hle : ∀ x, wireFn n C i x ≤ wireFn n C (n+j) x)
    (heq : ∀ u ∈ Q, wireFn n C i (singletonInput u) =
      wireFn n C (n+j) (singletonInput u))
    (w : ℕ) (hstar : ∀ x, wireFn n C w x = starFun Q x) :
    ∀ x, wireFn n (replace C j i) w x = starFun Q x := by
  intro x
  cases hx : starFun Q x with
  | false =>
      have h := replace_wire_le_at n C hC j hj i hi x (hle x) w
      rw [hstar, hx] at h
      exact le_antisymm h (by cases wireFn n (replace C j i) w x <;> decide)
  | true =>
      obtain ⟨u,hu,hux⟩ := (of_decide_eq_true hx : ∃ u ∈ Q, x u = true)
      have hsingle : wireFn n C w (singletonInput u) = true := by
        rw [hstar]
        apply decide_eq_true
        exact ⟨u,hu,by simp [singletonInput]⟩
      have hnew : wireFn n (replace C j i) w (singletonInput u) = true := by
        rw [replace_wire_eq n C j hj i hi _ (heq u hu) w]
        exact hsingle
      exact Bool.le_iff_imp.mp (replace_wire_mono n C hC j i w (singletonInput_le u x hux)) hnew

lemma replace_keepsStars (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (i : ℕ) (hi : i < n+j)
    (hle : ∀ x, wireFn n C i x ≤ wireFn n C (n+j) x)
    (heq : ∀ u : Fin n, wireFn n C i (singletonInput u) =
      wireFn n C (n+j) (singletonInput u)) : KeepsStars n C (replace C j i) := by
  intro Q w hQ hstar
  exact ⟨w, replace_star_preserved n Q C hC j hj i hi hle (fun u _ => heq u) w hstar⟩

end H5OrReplace


namespace H5OrReplace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.TwoColour H5Pruning H5Bridge H5Stars

lemma replace_admissible {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : admissible p l E C)
    (j : ℕ) (hj : j < C.gates.length) (i : ℕ) (hi : i < p+l+j)
    (hop : (gateAt C j).op = .or)
    (hreach : orIn (p+l) C i ⊆ orIn (p+l) C (p+l+j))
    (hle : ∀ x, wireFn (p+l) C i x ≤ wireFn (p+l) C (p+l+j) x)
    (hedge : ∀ a b, (a,b) ∈ E →
      wireFn (p+l) C i (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) =
      wireFn (p+l) C (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)))
    (hsingle : ∀ u : Fin (p+l), wireFn (p+l) C i (singletonInput u) =
      wireFn (p+l) C (p+l+j) (singletonInput u)) :
    admissible p l E (replace C j i) := by
  have hspec : ∀ x, wireFn (p+l) C C.output x = H5Pruning.graphFun (bipartiteEdges E) x := by
    intro x
    rw [graphFun_bipartite]
    exact hC.2.1 x
  have hedge' : ∀ e ∈ bipartiteEdges E,
      wireFn (p+l) C i (pairInput e.1 e.2) = wireFn (p+l) C (p+l+j) (pairInput e.1 e.2) := by
    intro e he
    obtain ⟨ab,hab,rfl⟩ := Finset.mem_image.mp he
    exact hedge ab.1 ab.2 hab
  apply admissible_of_keeps E C (replace C j i) hC (replace_good (p+l) C hC.1 j hj i hi hop)
  · intro x
    change wireFn (p+l) (replace C j i) C.output x = wireFn (p+l) C C.output x
    rw [replace_graph_preserved (p+l) (bipartiteEdges E) C hC.1 j hj i hi hle hedge' C.output hspec x,
      hspec x]
  · exact replace_tCount_zero (p+l) C hC.1 j hj i hi hop _ hreach hC.2.2.1
  · exact replace_keepsStars (p+l) C hC.1 j hj i hi hle hsingle

end H5OrReplace

namespace H5SemanticScore

open PEqualNP.CircuitLowerBounds H5Pruning

noncomputable def truthSet (n : ℕ) (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter fun x => f x = true

noncomputable def truthCard (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ :=
  (truthSet n f).card

noncomputable def score (n : ℕ) (C : Circuit) : ℕ :=
  ∑ j ∈ Finset.range C.gates.length, truthCard n (wireFn n C (n+j))

lemma truthSet_subset (n : ℕ) (f g : (Fin n → Bool) → Bool)
    (hle : ∀ x, f x ≤ g x) : truthSet n f ⊆ truthSet n g := by
  classical
  intro x hx
  simp only [truthSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact Bool.le_iff_imp.mp (hle x) hx

lemma truthCard_le (n : ℕ) (f g : (Fin n → Bool) → Bool)
    (hle : ∀ x, f x ≤ g x) : truthCard n f ≤ truthCard n g :=
  Finset.card_le_card (truthSet_subset n f g hle)

lemma truthCard_lt (n : ℕ) (f g : (Fin n → Bool) → Bool)
    (hle : ∀ x, f x ≤ g x) (x : Fin n → Bool) (hf : f x = false) (hg : g x = true) :
    truthCard n f < truthCard n g := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨truthSet_subset n f g hle, ?_⟩
  intro heq
  have hx : x ∈ truthSet n g := by simp [truthSet, hg]
  rw [← heq] at hx
  simp [truthSet, hf] at hx

lemma score_le (n : ℕ) (C D : Circuit) (hlen : D.gates.length = C.gates.length)
    (hle : ∀ j < C.gates.length, ∀ x, wireFn n D (n+j) x ≤ wireFn n C (n+j) x) :
    score n D ≤ score n C := by
  unfold score
  rw [hlen]
  apply Finset.sum_le_sum
  intro j hj
  exact truthCard_le n _ _ (hle j (Finset.mem_range.mp hj))

lemma score_lt (n : ℕ) (C D : Circuit) (hlen : D.gates.length = C.gates.length)
    (hle : ∀ k < C.gates.length, ∀ x, wireFn n D (n+k) x ≤ wireFn n C (n+k) x)
    (j : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool)
    (hold : wireFn n C (n+j) x = true) (hnew : wireFn n D (n+j) x = false) :
    score n D < score n C := by
  unfold score
  rw [hlen]
  apply Finset.sum_lt_sum
  · intro k hk
    exact truthCard_le n _ _ (hle k (Finset.mem_range.mp hk))
  · exact ⟨j, Finset.mem_range.mpr hj, truthCard_lt n _ _ (hle j hj) x hnew hold⟩

lemma gate_eq_of_score_le (n : ℕ) (C D : Circuit)
    (hlen : D.gates.length = C.gates.length)
    (hle : ∀ k < C.gates.length, ∀ x, wireFn n D (n+k) x ≤ wireFn n C (n+k) x)
    (hscore : score n C ≤ score n D) (j : ℕ) (hj : j < C.gates.length)
    (x : Fin n → Bool) : wireFn n D (n+j) x = wireFn n C (n+j) x := by
  cases hold : wireFn n C (n+j) x with
  | false =>
      have h := hle j hj x
      rw [hold] at h
      cases hnew : wireFn n D (n+j) x with
      | false => rfl
      | true =>
          rw [hnew] at h
          have ht := Bool.le_iff_imp.mp h rfl
          cases ht
  | true =>
      cases hnew : wireFn n D (n+j) x with
      | true => rfl
      | false =>
          have hlt := score_lt n C D hlen hle j hj x hold hnew
          omega

lemma exists_four_minima {α : Type} (P : α → Prop) (f g h k : α → ℕ)
    (hex : ∃ a, P a) :
    ∃ a, P a ∧ (∀ b, P b → f a ≤ f b) ∧
      (∀ b, P b → f b = f a → g a ≤ g b) ∧
      (∀ b, P b → f b = f a → g b = g a → h a ≤ h b) ∧
      (∀ b, P b → f b = f a → g b = g a → h b = h a → k a ≤ k b) := by
  obtain ⟨a₀, ha₀, hf₀, hg₀, hh₀⟩ := H5Minimum.exists_three_minima P f g h hex
  obtain ⟨a, ⟨ha, hef, heg, heh⟩, hk⟩ :=
    H5Minimum.exists_minimizer
      (fun a => P a ∧ f a = f a₀ ∧ g a = g a₀ ∧ h a = h a₀) k
      ⟨a₀, ha₀, rfl, rfl, rfl⟩
  refine ⟨a, ha, ?_, ?_, ?_, ?_⟩
  · intro b hb
    rw [hef]
    exact hf₀ b hb
  · intro b hb hebf
    rw [heg]
    exact hg₀ b hb (hebf.trans hef)
  · intro b hb hebf hebg
    rw [heh]
    exact hh₀ b hb (hebf.trans hef) (hebg.trans heg)
  · intro b hb hebf hebg hebh
    exact hk b ⟨hb, hebf.trans hef, hebg.trans heg, hebh.trans heh⟩

open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm H5Stars H5Normalize

lemma normal_of_three_minima (n : ℕ) (F : (Fin n → Bool) → Bool) (lin : ℕ → Bool)
    (hsingle : ∀ a : Fin n, F (singletonInput a) = false)
    (hpos : ∃ x, F x = true) (P : Circuit → Prop) (D : Circuit) (hD : P D)
    (hgood : ∀ A, P A → good n F lin A)
    (hclosed : ∀ A B, P A → good n F lin B → KeepsStars n A B → P B)
    (hsize : ∀ A, P A → D.size ≤ A.size)
    (hcount : ∀ A, P A → A.size = D.size → H5Count.andCount D.gates ≤ H5Count.andCount A.gates)
    (hindex : ∀ A, P A → A.size = D.size →
      H5Count.andCount A.gates = H5Count.andCount D.gates →
      H5OrLift.andIndexSum D ≤ H5OrLift.andIndexSum A) : normal n F D := by
  obtain ⟨hAO, hspec, hT⟩ := hgood D hD
  intro i hi j hj hiAnd hBelow hjAnd hcone
  obtain ⟨g, hig, hgj, hg, hmem⟩ := H5OrLift.exists_direct_reader n D i j hj hcone
  have hgAO : (gateAt D g).op = GateOp.and ∨ (gateAt D g).op = GateOp.or := by
    rw [H5OrLift.gateAt_eq_getElem D g hg]
    exact hAO.1 D.gates[g] (List.getElem_mem hg)
  rcases hgAO with hgAnd | hgOr
  · obtain ⟨D', hAO', hsize', hcount', hspec', hT', hstars⟩ :=
      H5Stars.and_reader_lift_keeps n D hAO F hsingle hspec (n+i) g hg hgAnd hmem hBelow lin hT
    have hPD' : P D' := hclosed D D' hD ⟨hAO', hspec', hT'⟩ hstars
    have hsz : D'.size = D.size := Nat.le_antisymm hsize' (hsize D' hPD')
    have hcnt := hcount D' hPD' hsz
    omega
  · have hgj' : g < j := by
      by_contra hge
      have heq : g = j := by omega
      rw [heq, hjAnd] at hgOr
      cases hgOr
    obtain ⟨D', hAO', hsize', hcount', hspec', hT', hstars, hindex'⟩ :=
      H5OrLiftWrap.or_reader_lift_keeps n D hAO F hsingle hspec
        (valid_output n F D hspec hpos) i g j hig hgj' hj hiAnd hgOr hjAnd hmem hBelow lin hT
    have hPD' : P D' := hclosed D D' hD ⟨hAO', hspec', hT'⟩ hstars
    have hidx := hindex D' hPD' hsize' hcount'
    omega

lemma normalize_with_score (n : ℕ) (F : (Fin n → Bool) → Bool) (lin : ℕ → Bool)
    (hsingle : ∀ a : Fin n, F (singletonInput a) = false)
    (hpos : ∃ x, F x = true) (P : Circuit → Prop) (C : Circuit) (hC : P C)
    (hgood : ∀ A, P A → good n F lin A)
    (hclosed : ∀ A B, P A → good n F lin B → KeepsStars n A B → P B) :
    ∃ D, P D ∧ D.size ≤ C.size ∧
      (∀ A, P A → D.size ≤ A.size) ∧
      (∀ A, P A → A.size = D.size → H5Count.andCount D.gates ≤ H5Count.andCount A.gates) ∧
      (∀ A, P A → A.size = D.size →
        H5Count.andCount A.gates = H5Count.andCount D.gates →
        H5OrLift.andIndexSum D ≤ H5OrLift.andIndexSum A) ∧
      (∀ A, P A → A.size = D.size →
        H5Count.andCount A.gates = H5Count.andCount D.gates →
        H5OrLift.andIndexSum A = H5OrLift.andIndexSum D → score n D ≤ score n A) ∧
      normal n F D := by
  obtain ⟨D, hD, hsize, hcount, hindex, hscore⟩ :=
    exists_four_minima P Circuit.size (fun A => H5Count.andCount A.gates)
      H5OrLift.andIndexSum (score n) ⟨C, hC⟩
  exact ⟨D, hD, hsize C hC, hsize, hcount, hindex, hscore,
    normal_of_three_minima n F lin hsingle hpos P D hD hgood hclosed hsize hcount hindex⟩

open H5Bridge

lemma normalize_admissible_with_score {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : E.Nonempty) (C : Circuit) (hC : admissible p l E C) :
    ∃ D, admissible p l E D ∧ D.size ≤ C.size ∧
      (∀ A, admissible p l E A → D.size ≤ A.size) ∧
      (∀ A, admissible p l E A → A.size = D.size →
        H5Count.andCount D.gates ≤ H5Count.andCount A.gates) ∧
      (∀ A, admissible p l E A → A.size = D.size →
        H5Count.andCount A.gates = H5Count.andCount D.gates →
        H5OrLift.andIndexSum D ≤ H5OrLift.andIndexSum A) ∧
      (∀ A, admissible p l E A → A.size = D.size →
        H5Count.andCount A.gates = H5Count.andCount D.gates →
        H5OrLift.andIndexSum A = H5OrLift.andIndexSum D → score (p+l) D ≤ score (p+l) A) ∧
      normal (p+l) (graphFun (bipartiteEdges E)) D := by
  classical
  let F := graphFun (bipartiteEdges E)
  have hpos : ∃ x, F x = true := by
    refine ⟨fun _ => true, ?_⟩
    rw [show F = graphFun (bipartiteEdges E) from rfl, graphFun_bipartite]
    obtain ⟨⟨a,b⟩,hab⟩ := hE
    exact decide_eq_true ⟨a,b,hab,rfl,rfl⟩
  have hgood : ∀ D, admissible p l E D → good (p+l) F (fun i => decide (p ≤ i)) D := by
    intro D hD
    refine ⟨hD.1, ?_, hD.2.2.1⟩
    intro x
    rw [show F x = graphFun (bipartiteEdges E) x from rfl, graphFun_bipartite]
    exact hD.2.1 x
  have hclosed : ∀ D D', admissible p l E D →
      good (p+l) F (fun i => decide (p ≤ i)) D' → KeepsStars (p+l) D D' →
      admissible p l E D' := by
    intro D D' hD hD' hstars
    apply admissible_of_keeps E D D' hD hD'.1 _ hD'.2.2 hstars
    intro x
    exact (hD'.2.1 x).trans ((hgood D hD).2.1 x).symm
  exact normalize_with_score (p+l) F (fun i => decide (p ≤ i))
    (bipartite_false_singletons E) hpos (admissible p l E) C hC hgood hclosed

end H5SemanticScore


namespace H5Owners

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm H5Pruning

def leftBound {p l : ℕ} (E : Finset (Fin p × Fin l))
    (f : (Fin (p+l) → Bool) → Bool) (a : Fin p) : Prop :=
  ∀ x, f x = true → ∃ b : Fin l, (a,b) ∈ E ∧ x (Fin.natAdd p b) = true

def rightBound {p l : ℕ} (E : Finset (Fin p × Fin l))
    (f : (Fin (p+l) → Bool) → Bool) (b : Fin l) : Prop :=
  ∀ x, f x = true → ∃ a : Fin p, (a,b) ∈ E ∧ x (Fin.castAdd l a) = true

lemma right_injective {p l : ℕ} : Function.Injective (Fin.natAdd p : Fin l → Fin (p+l)) := by
  intro a b h
  apply Fin.ext
  have he := congrArg Fin.val h
  simp only [Fin.val_natAdd] at he
  omega

lemma left_injective {p l : ℕ} : Function.Injective (Fin.castAdd l : Fin p → Fin (p+l)) := by
  intro a b h
  exact Fin.ext (congrArg (fun z : Fin (p+l) => z.val) h)

lemma left_right_distinct {p l : ℕ} (a : Fin p) (b : Fin l) :
    Fin.castAdd l a ≠ Fin.natAdd p b := by
  intro h
  have he := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at he
  have ha := a.isLt
  omega

lemma true_singleton_lower {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hf : Monotone f) (q : Fin n) (hq : f (singletonInput q) = true) :
    ∀ x, x q = true → f x = true := by
  intro x hx
  exact Bool.le_iff_imp.mp (hf (singletonInput_le q x hx)) hq

lemma left_two_bounds_agreement {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (f : (Fin (p+l) → Bool) → Bool) (hf : Monotone f)
    (a a' : Fin p) (hne : a ≠ a') (hb : leftBound E f a) (hb' : leftBound E f a')
    (q : Fin l) (hq : f (singletonInput (Fin.natAdd p q)) = true) :
    (∀ x, x (Fin.natAdd p q) = true → f x = true) ∧
    (∀ u : Fin (p+l), f (singletonInput u) = singletonInput u (Fin.natAdd p q)) ∧
    (∀ u : Fin p, ∀ v : Fin l,
      f (pairInput (Fin.castAdd l u) (Fin.natAdd p v)) =
        pairInput (Fin.castAdd l u) (Fin.natAdd p v) (Fin.natAdd p q)) := by
  have haq : (a,q) ∈ E := by
    obtain ⟨b, hab, hval⟩ := hb _ hq
    have he : Fin.natAdd p b = Fin.natAdd p q := by simpa [singletonInput] using hval
    exact right_injective he ▸ hab
  have ha'q : (a',q) ∈ E := by
    obtain ⟨b, hab, hval⟩ := hb' _ hq
    have he : Fin.natAdd p b = Fin.natAdd p q := by simpa [singletonInput] using hval
    exact right_injective he ▸ hab
  have hunique : ∀ b : Fin l, (a,b) ∈ E → (a',b) ∈ E → b = q := by
    intro b hab ha'b
    by_contra hn
    exact hfour a a' b q hne hn ⟨hab,haq,ha'b,ha'q⟩
  have hlower := true_singleton_lower f hf (Fin.natAdd p q) hq
  refine ⟨hlower, ?_, ?_⟩
  · intro u
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hu
      obtain ⟨b,hbE,hbu⟩ := hb _ hu
      obtain ⟨b',hb'E,hb'u⟩ := hb' _ hu
      have he : Fin.natAdd p b = u := by simpa [singletonInput] using hbu
      have he' : Fin.natAdd p b' = u := by simpa [singletonInput] using hb'u
      have hbb' := right_injective (he.trans he'.symm)
      subst b'
      have hbq := hunique b hbE hb'E
      subst b
      simp [singletonInput,he]
    · exact hlower _
  · intro u v
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro huv
      obtain ⟨b,hbE,hbv⟩ := hb _ huv
      obtain ⟨b',hb'E,hb'v⟩ := hb' _ huv
      have get_right : ∀ c : Fin l,
          pairInput (Fin.castAdd l u) (Fin.natAdd p v) (Fin.natAdd p c) = true → c = v := by
        intro c hc
        have he : Fin.natAdd p c = Fin.castAdd l u ∨ Fin.natAdd p c = Fin.natAdd p v := by
          simpa [pairInput] using hc
        rcases he with he | he
        · exact False.elim (left_right_distinct u c he.symm)
        · exact right_injective he
      have hbv' := get_right b hbv
      have hb'v' := get_right b' hb'v
      subst b
      subst b'
      have hvq := hunique v hbE hb'E
      subst v
      simp [pairInput]
    · exact hlower _

lemma right_two_bounds_agreement {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (f : (Fin (p+l) → Bool) → Bool) (hf : Monotone f)
    (b b' : Fin l) (hne : b ≠ b') (hb : rightBound E f b) (hb' : rightBound E f b')
    (q : Fin p) (hq : f (singletonInput (Fin.castAdd l q)) = true) :
    (∀ x, x (Fin.castAdd l q) = true → f x = true) ∧
    (∀ u : Fin (p+l), f (singletonInput u) = singletonInput u (Fin.castAdd l q)) ∧
    (∀ u : Fin p, ∀ v : Fin l,
      f (pairInput (Fin.castAdd l u) (Fin.natAdd p v)) =
        pairInput (Fin.castAdd l u) (Fin.natAdd p v) (Fin.castAdd l q)) := by
  have hqb : (q,b) ∈ E := by
    obtain ⟨a, hab, hval⟩ := hb _ hq
    have he : Fin.castAdd l a = Fin.castAdd l q := by simpa [singletonInput] using hval
    exact left_injective he ▸ hab
  have hqb' : (q,b') ∈ E := by
    obtain ⟨a, hab, hval⟩ := hb' _ hq
    have he : Fin.castAdd l a = Fin.castAdd l q := by simpa [singletonInput] using hval
    exact left_injective he ▸ hab
  have hunique : ∀ a : Fin p, (a,b) ∈ E → (a,b') ∈ E → a = q := by
    intro a hab hab'
    by_contra hn
    exact hfour a q b b' hn hne ⟨hab,hab',hqb,hqb'⟩
  have hlower := true_singleton_lower f hf (Fin.castAdd l q) hq
  refine ⟨hlower, ?_, ?_⟩
  · intro u
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hu
      obtain ⟨a,hab,hau⟩ := hb _ hu
      obtain ⟨a',ha'b,hau'⟩ := hb' _ hu
      have he : Fin.castAdd l a = u := by simpa [singletonInput] using hau
      have he' : Fin.castAdd l a' = u := by simpa [singletonInput] using hau'
      have haa' := left_injective (he.trans he'.symm)
      subst a'
      have haq := hunique a hab ha'b
      subst a
      simp [singletonInput,he]
    · exact hlower _
  · intro u v
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro huv
      obtain ⟨a,hab,hav⟩ := hb _ huv
      obtain ⟨a',ha'b,hav'⟩ := hb' _ huv
      have get_left : ∀ c : Fin p,
          pairInput (Fin.castAdd l u) (Fin.natAdd p v) (Fin.castAdd l c) = true → c = u := by
        intro c hc
        have he : Fin.castAdd l c = Fin.castAdd l u ∨ Fin.castAdd l c = Fin.natAdd p v := by
          simpa [pairInput] using hc
        rcases he with he | he
        · exact left_injective he
        · exact False.elim (left_right_distinct c v he)
      have hau := get_left a hav
      have ha'u := get_left a' hav'
      subst a
      subst a'
      have huq := hunique u hab ha'b
      subst u
      simp [pairInput]
    · exact hlower _

end H5Owners

namespace H5Owners

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open H5Pruning H5Bridge H5AndReplace H5SemanticScore

def scoreMinimal {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit) : Prop :=
  ∀ D, admissible p l E D → D.size = C.size →
    H5Count.andCount D.gates = H5Count.andCount C.gates →
    H5OrLift.andIndexSum D = H5OrLift.andIndexSum C → score (p+l) C ≤ score (p+l) D

lemma replacement_fixed {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : admissible p l E C) (hmin : scoreMinimal E C)
    (j : ℕ) (hj : j < C.gates.length) (i : ℕ) (hi : i < p+l+j)
    (hop : (gateAt C j).op = .and)
    (hle : ∀ x, wireFn (p+l) C i x ≤ wireFn (p+l) C (p+l+j) x)
    (hedge : ∀ a b, (a,b) ∈ E →
      wireFn (p+l) C i (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) =
      wireFn (p+l) C (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)))
    (hsingle : ∀ u : Fin (p+l), wireFn (p+l) C i (singletonInput u) =
      wireFn (p+l) C (p+l+j) (singletonInput u)) :
    ∀ x, wireFn (p+l) C (p+l+j) x = wireFn (p+l) C i x := by
  let D := replace C j i
  have hD : admissible p l E D := replace_admissible E C hC j hj i hi hop hle hedge hsingle
  have hscore : score (p+l) C ≤ score (p+l) D :=
    hmin D hD (replace_size C j hj i) (replace_andCount C j hj i hop)
      (replace_andIndexSum C j hj i hop)
  have hweak := replace_wire_le (p+l) C hC.1 j hj i hi hle
  intro x
  have heq := gate_eq_of_score_le (p+l) C D (replace_length C j hj i)
    (fun k _ x => hweak (p+l+k) x) hscore j hj x
  rw [show wireFn (p+l) D (p+l+j) x = wireFn (p+l) C i x from
    replace_wire_self (p+l) C j hj i hi x] at heq
  exact heq.symm

lemma left_pure_of_score_minimal {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (C : Circuit) (hC : admissible p l E C) (hmin : scoreMinimal E C)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = .and)
    (a a' : Fin p) (hne : a ≠ a')
    (hb : leftBound E (wireFn (p+l) C (p+l+j)) a)
    (hb' : leftBound E (wireFn (p+l) C (p+l+j)) a')
    (q : Fin l) (hq : wireFn (p+l) C (p+l+j) (singletonInput (Fin.natAdd p q)) = true) :
    ∀ x, wireFn (p+l) C (p+l+j) x = x (Fin.natAdd p q) := by
  let u : Fin (p+l) := Fin.natAdd p q
  have h := left_two_bounds_agreement E hfour (wireFn (p+l) C (p+l+j))
    (wireFn_mono _ C hC.1 _) a a' hne hb hb' q hq
  have hi : u.val < p+l+j := by have hu := u.isLt; omega
  have hinput : ∀ x, wireFn (p+l) C u.val x = x u := fun x => wireFn_input _ C u.val u.isLt x
  have hle : ∀ x, wireFn (p+l) C u.val x ≤ wireFn (p+l) C (p+l+j) x := by
    intro x
    rw [hinput]
    exact Bool.le_iff_imp.mpr (h.1 x)
  have heq := replacement_fixed E C hC hmin j hj u.val hi hop hle
    (fun a b _ => by rw [hinput]; exact (h.2.2 a b).symm)
    (fun v => by rw [hinput]; exact (h.2.1 v).symm)
  intro x
  exact (heq x).trans (hinput x)

lemma right_pure_of_score_minimal {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (C : Circuit) (hC : admissible p l E C) (hmin : scoreMinimal E C)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = .and)
    (b b' : Fin l) (hne : b ≠ b')
    (hb : rightBound E (wireFn (p+l) C (p+l+j)) b)
    (hb' : rightBound E (wireFn (p+l) C (p+l+j)) b')
    (q : Fin p) (hq : wireFn (p+l) C (p+l+j) (singletonInput (Fin.castAdd l q)) = true) :
    ∀ x, wireFn (p+l) C (p+l+j) x = x (Fin.castAdd l q) := by
  let u : Fin (p+l) := Fin.castAdd l q
  have h := right_two_bounds_agreement E hfour (wireFn (p+l) C (p+l+j))
    (wireFn_mono _ C hC.1 _) b b' hne hb hb' q hq
  have hi : u.val < p+l+j := by have hu := u.isLt; omega
  have hinput : ∀ x, wireFn (p+l) C u.val x = x u := fun x => wireFn_input _ C u.val u.isLt x
  have hle : ∀ x, wireFn (p+l) C u.val x ≤ wireFn (p+l) C (p+l+j) x := by
    intro x
    rw [hinput]
    exact Bool.le_iff_imp.mpr (h.1 x)
  have heq := replacement_fixed E C hC hmin j hj u.val hi hop hle
    (fun a b _ => by rw [hinput]; exact (h.2.2 a b).symm)
    (fun v => by rw [hinput]; exact (h.2.1 v).symm)
  intro x
  exact (heq x).trans (hinput x)

end H5Owners

namespace H5Owners

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open H5Pruning H5Bridge H5SemanticScore

def multiOwnerPure {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit) : Prop :=
  ∀ j < C.gates.length, (gateAt C j).op = .and →
    (∀ (a a' : Fin p), a ≠ a' →
      leftBound E (wireFn (p+l) C (p+l+j)) a → leftBound E (wireFn (p+l) C (p+l+j)) a' →
      ∀ q : Fin l, wireFn (p+l) C (p+l+j) (singletonInput (Fin.natAdd p q)) = true →
        ∀ x, wireFn (p+l) C (p+l+j) x = x (Fin.natAdd p q)) ∧
    (∀ (b b' : Fin l), b ≠ b' →
      rightBound E (wireFn (p+l) C (p+l+j)) b → rightBound E (wireFn (p+l) C (p+l+j)) b' →
      ∀ q : Fin p, wireFn (p+l) C (p+l+j) (singletonInput (Fin.castAdd l q)) = true →
        ∀ x, wireFn (p+l) C (p+l+j) x = x (Fin.castAdd l q))

lemma multiOwnerPure_of_score_minimal {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (C : Circuit) (hC : admissible p l E C) (hmin : scoreMinimal E C) : multiOwnerPure E C := by
  intro j hj hop
  exact ⟨left_pure_of_score_minimal E hfour C hC hmin j hj hop,
    right_pure_of_score_minimal E hfour C hC hmin j hj hop⟩

lemma exists_normal_multiOwnerPure {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : E.Nonempty)
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (C : Circuit) (hC : admissible p l E C) :
    ∃ D : Circuit, admissible p l E D ∧ D.size ≤ C.size ∧
      (∀ A, admissible p l E A → D.size ≤ A.size) ∧
      H5Normalize.normal (p+l) (graphFun (bipartiteEdges E)) D ∧ scoreMinimal E D ∧
      multiOwnerPure E D ∧
      (∀ j < D.gates.length, ∃ (a : Fin p) (b : Fin l), (a,b) ∈ E ∧
        wireFn (p+l) D (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true) ∧
      ∀ j < D.gates.length,
        (∀ u : Fin (p+l), wireFn (p+l) D (p+l+j) (singletonInput u) = false) →
        ∃ (a : Fin p) (b : Fin l), (a,b) ∈ E ∧
          wireFn (p+l) D (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true ∧
          wireFn (p+l) (zeroed D j) D.output (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = false := by
  obtain ⟨D,hD,hsize,hmin,_,_,hscore,hnormal⟩ := normalize_admissible_with_score E hE C hC
  refine ⟨D,hD,hsize,hmin,hnormal,hscore,multiOwnerPure_of_score_minimal E hfour D hD hscore,?_,?_⟩
  · intro j hj
    by_contra hbad
    have hz : ∀ a b, (a,b) ∈ E →
        wireFn (p+l) D (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = false := by
      intro a b hab
      cases hv : wireFn (p+l) D (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) with
      | false => rfl
      | true => exact False.elim (hbad ⟨a,b,hab,hv⟩)
    obtain ⟨A,hA,hlt⟩ := prune_admissible E hE D hD j hj hz
    have hle := hmin A hA
    omega
  · intro j hj hsingle
    exact H5Essential.zero_singleton_gate_essential E D hD hmin j hj hsingle

end H5Owners

namespace H5Owners

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open H5Pruning H5Bridge H5SemanticScore

lemma or_replacement_fixed {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : admissible p l E C) (hmin : scoreMinimal E C)
    (j : ℕ) (hj : j < C.gates.length) (i : ℕ) (hi : i < p+l+j)
    (hop : (gateAt C j).op = .or)
    (hreach : orIn (p+l) C i ⊆ orIn (p+l) C (p+l+j))
    (hle : ∀ x, wireFn (p+l) C i x ≤ wireFn (p+l) C (p+l+j) x)
    (hedge : ∀ a b, (a,b) ∈ E →
      wireFn (p+l) C i (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) =
      wireFn (p+l) C (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)))
    (hsingle : ∀ u : Fin (p+l), wireFn (p+l) C i (singletonInput u) =
      wireFn (p+l) C (p+l+j) (singletonInput u)) :
    ∀ x, wireFn (p+l) C (p+l+j) x = wireFn (p+l) C i x := by
  let D := H5OrReplace.replace C j i
  have hD : admissible p l E D :=
    H5OrReplace.replace_admissible E C hC j hj i hi hop hreach hle hedge hsingle
  have hscore : score (p+l) C ≤ score (p+l) D :=
    hmin D hD (H5OrReplace.replace_size C j hj i) (H5OrReplace.replace_andCount C j hj i hop)
      (H5OrReplace.replace_andIndexSum C j hj i hop)
  have hweak := H5OrReplace.replace_wire_le (p+l) C hC.1 j hj i hi hle
  intro x
  have heq := gate_eq_of_score_le (p+l) C D (H5OrReplace.replace_length C j hj i)
    (fun k _ x => hweak (p+l+k) x) hscore j hj x
  rw [show wireFn (p+l) D (p+l+j) x = wireFn (p+l) C i x from
    H5OrReplace.replace_wire_self (p+l) C j hj i hi x] at heq
  exact heq.symm

lemma or_child_imp {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = .or)
    (v : ℕ) (hv : v ∈ (gateAt C j).inputs) (x : Fin n → Bool)
    (hval : wireFn n C v x = true) : wireFn n C (n+j) x = true := by
  rw [H5LiftGlue.wireFn_gate n C hC.2.1 j hj,hop]
  simp only [GateOp.eval,List.any_eq_true,List.mem_map,id_eq]
  exact ⟨true,⟨v,hv,hval⟩,rfl⟩

lemma pure_of_agreements {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : admissible p l E C) (hmin : scoreMinimal E C)
    (q : Fin (p+l)) (P : ℕ → Prop)
    (hchild : ∀ j < C.gates.length, (gateAt C j).op = .or →
      ∀ v ∈ (gateAt C j).inputs, P (p+l+j) → P v)
    (hagree : ∀ w, P w → wireFn (p+l) C w (singletonInput q) = true →
      (∀ x, x q = true → wireFn (p+l) C w x = true) ∧
      (∀ u, wireFn (p+l) C w (singletonInput u) = singletonInput u q) ∧
      (∀ a b, wireFn (p+l) C w (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) =
        pairInput (Fin.castAdd l a) (Fin.natAdd p b) q)) :
    ∀ w, P w → wireFn (p+l) C w (singletonInput q) = true →
      ∀ x, wireFn (p+l) C w x = x q := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hP hq
    by_cases hin : w < p+l
    · have he : (⟨w,hin⟩ : Fin (p+l)) = q := by
        rw [wireFn_input (p+l) C w hin] at hq
        simpa [singletonInput] using hq
      intro x
      rw [wireFn_input (p+l) C w hin,he]
    · have hvalid : w < p+l+C.gates.length := by
        by_contra hn
        rw [wireFn_ge (p+l) C w (by omega)] at hq
        cases hq
      let j := w-(p+l)
      have hj : j < C.gates.length := by omega
      have hw : p+l+j = w := by omega
      obtain ⟨u,v,hu,hv,hinp,hop,hval⟩ := binary_gate (p+l) C hC.1 j hj
      have ha := hagree w hP hq
      rcases hop with hop | hop
      · have hi : q.val < p+l+j := by have hqq := q.isLt; omega
        have hinput : ∀ x, wireFn (p+l) C q.val x = x q := fun x => wireFn_input _ C q.val q.isLt x
        have hl : ∀ x, wireFn (p+l) C q.val x ≤ wireFn (p+l) C (p+l+j) x := by
          intro x
          rw [hinput,hw]
          exact Bool.le_iff_imp.mpr (ha.1 x)
        have he := replacement_fixed E C hC hmin j hj q.val hi hop hl
          (fun a b _ => by rw [hinput,hw]; exact (ha.2.2 a b).symm)
          (fun a => by rw [hinput,hw]; exact (ha.2.1 a).symm)
        intro x
        rw [←hw,he x,hinput]
      · have hpos : wireFn (p+l) C u (singletonInput q) = true ∨
            wireFn (p+l) C v (singletonInput q) = true := by
          have he := hval (singletonInput q)
          rw [hw,hq] at he
          simpa [hop,GateOp.eval] using he.symm
        have step : ∀ k ∈ (gateAt C j).inputs,
            wireFn (p+l) C k (singletonInput q) = true →
            ∀ x, wireFn (p+l) C w x = x q := by
          intro k hk hkq
          have hkw : k < w := by have hh := hC.1.2.1 j hj k hk; omega
          have hkP : P k := hchild j hj hop k hk (by simpa [hw] using hP)
          have hkfun := ih k hkw hkP hkq
          have hr : orIn (p+l) C k ⊆ orIn (p+l) C (p+l+j) := by
            intro a ha
            exact H5Reach.orIn_up (p+l) C j k a hj hop hk (by omega) ha
          have hl : ∀ x, wireFn (p+l) C k x ≤ wireFn (p+l) C (p+l+j) x := by
            intro x
            rw [hkfun x,hw]
            exact Bool.le_iff_imp.mpr (ha.1 x)
          have he := or_replacement_fixed E C hC hmin j hj k (by omega) hop hr hl
            (fun a b _ => by rw [hkfun,hw]; exact (ha.2.2 a b).symm)
            (fun a => by rw [hkfun,hw]; exact (ha.2.1 a).symm)
          intro x
          rw [←hw,he x,hkfun]
        rcases hpos with huq | hvq
        · exact step u (by simp [hinp]) huq
        · exact step v (by simp [hinp]) hvq

end H5Owners

namespace H5Owners

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open H5Pruning H5Bridge H5SemanticScore

lemma left_all_wires_pure {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (C : Circuit) (hC : admissible p l E C) (hmin : scoreMinimal E C)
    (a a' : Fin p) (hne : a ≠ a') (q : Fin l) :
    ∀ w, leftBound E (wireFn (p+l) C w) a → leftBound E (wireFn (p+l) C w) a' →
      wireFn (p+l) C w (singletonInput (Fin.natAdd p q)) = true →
      ∀ x, wireFn (p+l) C w x = x (Fin.natAdd p q) := by
  have h := pure_of_agreements E C hC hmin (Fin.natAdd p q)
    (fun w => leftBound E (wireFn (p+l) C w) a ∧ leftBound E (wireFn (p+l) C w) a')
    (by
      intro j hj hop v hv hP
      exact ⟨fun x hx => hP.1 x (or_child_imp C hC.1 j hj hop v hv x hx),
        fun x hx => hP.2 x (or_child_imp C hC.1 j hj hop v hv x hx)⟩)
    (fun w hP hq => left_two_bounds_agreement E hfour (wireFn (p+l) C w)
      (wireFn_mono _ C hC.1 _) a a' hne hP.1 hP.2 q hq)
  intro w h₁ h₂ hq
  exact h w ⟨h₁,h₂⟩ hq

lemma right_all_wires_pure {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (C : Circuit) (hC : admissible p l E C) (hmin : scoreMinimal E C)
    (b b' : Fin l) (hne : b ≠ b') (q : Fin p) :
    ∀ w, rightBound E (wireFn (p+l) C w) b → rightBound E (wireFn (p+l) C w) b' →
      wireFn (p+l) C w (singletonInput (Fin.castAdd l q)) = true →
      ∀ x, wireFn (p+l) C w x = x (Fin.castAdd l q) := by
  have h := pure_of_agreements E C hC hmin (Fin.castAdd l q)
    (fun w => rightBound E (wireFn (p+l) C w) b ∧ rightBound E (wireFn (p+l) C w) b')
    (by
      intro j hj hop v hv hP
      exact ⟨fun x hx => hP.1 x (or_child_imp C hC.1 j hj hop v hv x hx),
        fun x hx => hP.2 x (or_child_imp C hC.1 j hj hop v hv x hx)⟩)
    (fun w hP hq => right_two_bounds_agreement E hfour (wireFn (p+l) C w)
      (wireFn_mono _ C hC.1 _) b b' hne hP.1 hP.2 q hq)
  intro w h₁ h₂ hq
  exact h w ⟨h₁,h₂⟩ hq

def allOwnerPure {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit) : Prop :=
    (∀ (a a' : Fin p), a ≠ a' → ∀ q : Fin l,
      ∀ w, leftBound E (wireFn (p+l) C w) a → leftBound E (wireFn (p+l) C w) a' →
        wireFn (p+l) C w (singletonInput (Fin.natAdd p q)) = true →
          ∀ x, wireFn (p+l) C w x = x (Fin.natAdd p q)) ∧
    (∀ (b b' : Fin l), b ≠ b' → ∀ q : Fin p,
      ∀ w, rightBound E (wireFn (p+l) C w) b → rightBound E (wireFn (p+l) C w) b' →
        wireFn (p+l) C w (singletonInput (Fin.castAdd l q)) = true →
          ∀ x, wireFn (p+l) C w x = x (Fin.castAdd l q))

lemma exists_normal_allOwnerPure {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : E.Nonempty)
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (C : Circuit) (hC : admissible p l E C) :
    ∃ D : Circuit, admissible p l E D ∧ D.size ≤ C.size ∧
      (∀ A, admissible p l E A → D.size ≤ A.size) ∧
      H5Normalize.normal (p+l) (graphFun (bipartiteEdges E)) D ∧ scoreMinimal E D ∧
      allOwnerPure E D ∧
      (∀ j < D.gates.length, ∃ (a : Fin p) (b : Fin l), (a,b) ∈ E ∧
        wireFn (p+l) D (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true) ∧
      ∀ j < D.gates.length,
        (∀ u : Fin (p+l), wireFn (p+l) D (p+l+j) (singletonInput u) = false) →
        ∃ (a : Fin p) (b : Fin l), (a,b) ∈ E ∧
          wireFn (p+l) D (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true ∧
          wireFn (p+l) (zeroed D j) D.output (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = false := by
  obtain ⟨D,hD,hsize,hmin,hN,hscore,_,hactive,hessential⟩ :=
    exists_normal_multiOwnerPure E hE hfour C hC
  exact ⟨D,hD,hsize,hmin,hN,hscore,
    ⟨left_all_wires_pure E hfour D hD hscore,right_all_wires_pure E hfour D hD hscore⟩,
    hactive,hessential⟩

end H5Owners

namespace H5Owners

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open H5Pruning H5Bridge H5SemanticScore

lemma pure_of_edge_agreements {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : admissible p l E C) (hmin : scoreMinimal E C)
    (q : Fin (p+l)) (P : ℕ → Prop)
    (hchild : ∀ j < C.gates.length, (gateAt C j).op = .or →
      ∀ v ∈ (gateAt C j).inputs, P (p+l+j) → P v)
    (hagree : ∀ w, P w → wireFn (p+l) C w (singletonInput q) = true →
      (∀ x, x q = true → wireFn (p+l) C w x = true) ∧
      (∀ u, wireFn (p+l) C w (singletonInput u) = singletonInput u q) ∧
      (∀ a b, (a,b) ∈ E → wireFn (p+l) C w (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) =
        pairInput (Fin.castAdd l a) (Fin.natAdd p b) q)) :
    ∀ w, P w → wireFn (p+l) C w (singletonInput q) = true →
      ∀ x, wireFn (p+l) C w x = x q := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hP hq
    by_cases hin : w < p+l
    · have he : (⟨w,hin⟩ : Fin (p+l)) = q := by
        rw [wireFn_input (p+l) C w hin] at hq
        simpa [singletonInput] using hq
      intro x
      rw [wireFn_input (p+l) C w hin,he]
    · have hvalid : w < p+l+C.gates.length := by
        by_contra hn
        rw [wireFn_ge (p+l) C w (by omega)] at hq
        cases hq
      let j := w-(p+l)
      have hj : j < C.gates.length := by omega
      have hw : p+l+j = w := by omega
      obtain ⟨u,v,hu,hv,hinp,hop,hval⟩ := binary_gate (p+l) C hC.1 j hj
      have ha := hagree w hP hq
      rcases hop with hop | hop
      · have hi : q.val < p+l+j := by have hqq := q.isLt; omega
        have hinput : ∀ x, wireFn (p+l) C q.val x = x q := fun x => wireFn_input _ C q.val q.isLt x
        have hl : ∀ x, wireFn (p+l) C q.val x ≤ wireFn (p+l) C (p+l+j) x := by
          intro x
          rw [hinput,hw]
          exact Bool.le_iff_imp.mpr (ha.1 x)
        have he := replacement_fixed E C hC hmin j hj q.val hi hop hl
          (fun a b hab => by rw [hinput,hw]; exact (ha.2.2 a b hab).symm)
          (fun a => by rw [hinput,hw]; exact (ha.2.1 a).symm)
        intro x
        rw [←hw,he x,hinput]
      · have hpos : wireFn (p+l) C u (singletonInput q) = true ∨
            wireFn (p+l) C v (singletonInput q) = true := by
          have he := hval (singletonInput q)
          rw [hw,hq] at he
          simpa [hop,GateOp.eval] using he.symm
        have step : ∀ k ∈ (gateAt C j).inputs,
            wireFn (p+l) C k (singletonInput q) = true →
            ∀ x, wireFn (p+l) C w x = x q := by
          intro k hk hkq
          have hkw : k < w := by have hh := hC.1.2.1 j hj k hk; omega
          have hkP : P k := hchild j hj hop k hk (by simpa [hw] using hP)
          have hkfun := ih k hkw hkP hkq
          have hr : orIn (p+l) C k ⊆ orIn (p+l) C (p+l+j) := by
            intro a ha
            exact H5Reach.orIn_up (p+l) C j k a hj hop hk (by omega) ha
          have hl : ∀ x, wireFn (p+l) C k x ≤ wireFn (p+l) C (p+l+j) x := by
            intro x
            rw [hkfun x,hw]
            exact Bool.le_iff_imp.mpr (ha.1 x)
          have he := or_replacement_fixed E C hC hmin j hj k (by omega) hop hr hl
            (fun a b hab => by rw [hkfun,hw]; exact (ha.2.2 a b hab).symm)
            (fun a => by rw [hkfun,hw]; exact (ha.2.1 a).symm)
          intro x
          rw [←hw,he x,hkfun]
        rcases hpos with huq | hvq
        · exact step u (by simp [hinp]) huq
        · exact step v (by simp [hinp]) hvq


lemma pure_of_singleton_edge_bounds {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : admissible p l E C) (hmin : scoreMinimal E C)
    (q : Fin (p+l)) (w : ℕ)
    (hq : wireFn (p+l) C w (singletonInput q) = true)
    (hsingle : ∀ u, wireFn (p+l) C w (singletonInput u) ≤ singletonInput u q)
    (hedge : ∀ a b, (a,b) ∈ E →
      wireFn (p+l) C w (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) ≤
        pairInput (Fin.castAdd l a) (Fin.natAdd p b) q) :
    ∀ x, wireFn (p+l) C w x = x q := by
  let P := fun v =>
    (∀ u, wireFn (p+l) C v (singletonInput u) ≤ singletonInput u q) ∧
    (∀ a b, (a,b) ∈ E →
      wireFn (p+l) C v (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) ≤
        pairInput (Fin.castAdd l a) (Fin.natAdd p b) q)
  have hchild : ∀ j < C.gates.length, (gateAt C j).op = .or →
      ∀ v ∈ (gateAt C j).inputs, P (p+l+j) → P v := by
    intro j hj hop v hv hP
    have hle : ∀ x, wireFn (p+l) C v x ≤ wireFn (p+l) C (p+l+j) x := by
      intro x
      exact Bool.le_iff_imp.mpr (or_child_imp C hC.1 j hj hop v hv x)
    exact ⟨fun u => (hle _).trans (hP.1 u),
      fun a b hab => (hle _).trans (hP.2 a b hab)⟩
  have hagree : ∀ v, P v → wireFn (p+l) C v (singletonInput q) = true →
      (∀ x, x q = true → wireFn (p+l) C v x = true) ∧
      (∀ u, wireFn (p+l) C v (singletonInput u) = singletonInput u q) ∧
      (∀ a b, (a,b) ∈ E →
        wireFn (p+l) C v (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) =
          pairInput (Fin.castAdd l a) (Fin.natAdd p b) q) := by
    intro v hP hvq
    have hlower := true_singleton_lower (wireFn (p+l) C v) (wireFn_mono _ C hC.1 v) q hvq
    refine ⟨hlower, ?_, ?_⟩
    · intro u
      exact le_antisymm (hP.1 u) (Bool.le_iff_imp.mpr (hlower _))
    · intro a b hab
      exact le_antisymm (hP.2 a b hab) (Bool.le_iff_imp.mpr (hlower _))
  exact pure_of_edge_agreements E C hC hmin q P hchild hagree w ⟨hsingle, hedge⟩ hq

lemma pure_of_singleton_edge_agreement {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : admissible p l E C) (hmin : scoreMinimal E C)
    (q : Fin (p+l)) (w : ℕ)
    (hsingle : ∀ u, wireFn (p+l) C w (singletonInput u) = singletonInput u q)
    (hedge : ∀ a b, (a,b) ∈ E →
      wireFn (p+l) C w (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) =
        pairInput (Fin.castAdd l a) (Fin.natAdd p b) q) :
    ∀ x, wireFn (p+l) C w x = x q := by
  apply pure_of_singleton_edge_bounds E C hC hmin q w
  · simpa [singletonInput] using hsingle q
  · intro u
    exact le_of_eq (hsingle u)
  · intro a b hab
    exact le_of_eq (hedge a b hab)

lemma singleton_residual_edge_of_agreement {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : admissible p l E C) (hmin : scoreMinimal E C)
    (q : Fin (p+l)) (w : ℕ)
    (hsingle : ∀ u, wireFn (p+l) C w (singletonInput u) = singletonInput u q)
    (hnotpure : ¬ ∀ x, wireFn (p+l) C w x = x q) :
    ∃ (a : Fin p) (b : Fin l), (a,b) ∈ E ∧
      wireFn (p+l) C w (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true ∧
      pairInput (Fin.castAdd l a) (Fin.natAdd p b) q = false := by
  by_contra hbad
  apply hnotpure
  apply pure_of_singleton_edge_bounds E C hC hmin q w
  · simpa [singletonInput] using hsingle q
  · intro u
    exact le_of_eq (hsingle u)
  · intro a b hab
    apply Bool.le_iff_imp.mpr
    intro hv
    cases hq : pairInput (Fin.castAdd l a) (Fin.natAdd p b) q with
    | true => rfl
    | false => exact False.elim (hbad ⟨a,b,hab,hv,hq⟩)

lemma singleton_residual_edge {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : admissible p l E C) (hmin : scoreMinimal E C)
    (q : Fin (p+l)) (w : ℕ)
    (hsupport : ∀ u, wireFn (p+l) C w (singletonInput u) = true ↔ u = q)
    (hnotpure : ¬ ∀ x, wireFn (p+l) C w x = x q) :
    ∃ (a : Fin p) (b : Fin l), (a,b) ∈ E ∧
      wireFn (p+l) C w (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true ∧
      pairInput (Fin.castAdd l a) (Fin.natAdd p b) q = false := by
  apply singleton_residual_edge_of_agreement E C hC hmin q w _ hnotpure
  intro u
  apply Bool.eq_iff_iff.mpr
  simp only [singletonInput, decide_eq_true_eq]
  exact (hsupport u).trans eq_comm

end H5Owners

namespace H5ReplacementEssential

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open H5Pruning H5Bridge H5Stars H5AndReplace H5SemanticScore H5Owners

lemma replacement_fixed_of_output {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : admissible p l E C) (hmin : scoreMinimal E C)
    (j : ℕ) (hj : j < C.gates.length) (i : ℕ) (hi : i < p+l+j)
    (hop : (gateAt C j).op = .and)
    (hle : ∀ x, wireFn (p+l) C i x ≤ wireFn (p+l) C (p+l+j) x)
    (hsingle : ∀ u : Fin (p+l), wireFn (p+l) C i (singletonInput u) =
      wireFn (p+l) C (p+l+j) (singletonInput u))
    (hout : ∀ x, wireFn (p+l) (replace C j i) C.output x = wireFn (p+l) C C.output x) :
    ∀ x, wireFn (p+l) C (p+l+j) x = wireFn (p+l) C i x := by
  let D := replace C j i
  have hD : admissible p l E D := by
    apply admissible_of_keeps E C D hC (replace_good (p+l) C hC.1 j hj i hi hop) hout
    · rw [show D = replace C j i from rfl, replace_tCount (p+l) C hC.1 j hj i hi hop]
      exact hC.2.2.1
    · exact replace_keepsStars (p+l) C hC.1 j hj i hi hle hsingle
  have hscore : score (p+l) C ≤ score (p+l) D :=
    hmin D hD (replace_size C j hj i) (replace_andCount C j hj i hop)
      (replace_andIndexSum C j hj i hop)
  have hweak := replace_wire_le (p+l) C hC.1 j hj i hi hle
  intro x
  have heq := gate_eq_of_score_le (p+l) C D (replace_length C j hj i)
    (fun k _ x => hweak (p+l+k) x) hscore j hj x
  rw [show wireFn (p+l) D (p+l+j) x = wireFn (p+l) C i x from
    replace_wire_self (p+l) C j hj i hi x] at heq
  exact heq.symm

lemma replacement_loss_values (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (i : ℕ) (hi : i < n+j) (x : Fin n → Bool)
    (hle : wireFn n C i x ≤ wireFn n C (n+j) x)
    (hold : wireFn n C C.output x = true)
    (hnew : wireFn n (replace C j i) C.output x = false) :
    wireFn n C i x = false ∧ wireFn n C (n+j) x = true := by
  have hne : wireFn n C i x ≠ wireFn n C (n+j) x := by
    intro heq
    have h := replace_wire_eq n C j hj i hi x heq C.output
    rw [hnew, hold] at h
    cases h
  cases hi0 : wireFn n C i x with
  | false =>
      refine ⟨rfl,?_⟩
      cases hj0 : wireFn n C (n+j) x with
      | false => exact (hne (hi0.trans hj0.symm)).elim
      | true => rfl
  | true =>
      have hj1 := Bool.le_iff_imp.mp hle hi0
      exact (hne (hi0.trans hj1.symm)).elim

lemma and_replacement_output_essential {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : admissible p l E C) (hmin : scoreMinimal E C)
    (j : ℕ) (hj : j < C.gates.length) (i : ℕ) (hi : i < p+l+j)
    (hop : (gateAt C j).op = .and)
    (hle : ∀ x, wireFn (p+l) C i x ≤ wireFn (p+l) C (p+l+j) x)
    (hsingle : ∀ u : Fin (p+l), wireFn (p+l) C i (singletonInput u) =
      wireFn (p+l) C (p+l+j) (singletonInput u))
    (hneq : ¬ ∀ x, wireFn (p+l) C (p+l+j) x = wireFn (p+l) C i x) :
    ∃ (a : Fin p) (b : Fin l), (a,b) ∈ E ∧
      wireFn (p+l) C i (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = false ∧
      wireFn (p+l) C (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true ∧
      wireFn (p+l) (replace C j i) C.output
        (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = false := by
  classical
  by_contra hbad
  have hspec : ∀ x, wireFn (p+l) C C.output x = H5Pruning.graphFun (bipartiteEdges E) x := by
    intro x
    rw [graphFun_bipartite]
    exact hC.2.1 x
  have hpos : ∀ a b, (a,b) ∈ E → wireFn (p+l) (replace C j i) C.output
      (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true := by
    intro a b hab
    cases hnew : wireFn (p+l) (replace C j i) C.output
      (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) with
    | true => rfl
    | false =>
        have hold : wireFn (p+l) C C.output
            (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true := by
          rw [hspec, graphFun_bipartite]
          exact decide_eq_true ⟨a,b,hab,by simp [pairInput],by simp [pairInput]⟩
        obtain ⟨hi0,hj1⟩ := replacement_loss_values (p+l) C j hj i hi _ (hle _) hold hnew
        exact (hbad ⟨a,b,hab,hi0,hj1,hnew⟩).elim
  have hfun : ∀ x, wireFn (p+l) (replace C j i) C.output x =
      H5Pruning.graphFun (bipartiteEdges E) x := by
    apply H5Essential.graph_eq_of_positive_and_le (p+l) (bipartiteEdges E) _
      (replace_wire_mono (p+l) C hC.1 j i C.output)
    · intro x
      rw [← hspec x]
      exact replace_wire_le_at (p+l) C hC.1 j hj i hi x (hle x) C.output
    · intro e he
      obtain ⟨ab,hab,rfl⟩ := Finset.mem_image.mp he
      exact hpos ab.1 ab.2 hab
  apply hneq
  apply replacement_fixed_of_output E C hC hmin j hj i hi hop hle hsingle
  intro x
  exact (hfun x).trans (hspec x).symm

lemma singleton_remainder_output_essential {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : admissible p l E C) (hmin : scoreMinimal E C)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = .and)
    (q : Fin (p+l))
    (hsingle : ∀ u : Fin (p+l), wireFn (p+l) C (p+l+j) (singletonInput u) = singletonInput u q)
    (hneq : ¬ ∀ x, wireFn (p+l) C (p+l+j) x = x q) :
    ∃ (a : Fin p) (b : Fin l), (a,b) ∈ E ∧
      pairInput (Fin.castAdd l a) (Fin.natAdd p b) q = false ∧
      wireFn (p+l) C (p+l+j) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true ∧
      wireFn (p+l) (replace C j q.val) C.output
        (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = false := by
  have hi : q.val < p+l+j := by have := q.isLt; omega
  have hinput : ∀ x, wireFn (p+l) C q.val x = x q :=
    fun x => wireFn_input (p+l) C q.val q.isLt x
  have hle : ∀ x, wireFn (p+l) C q.val x ≤ wireFn (p+l) C (p+l+j) x := by
    intro x
    rw [hinput]
    apply Bool.le_iff_imp.mpr
    intro hx
    have hq : wireFn (p+l) C (p+l+j) (singletonInput q) = true := by
      rw [hsingle]
      simp [singletonInput]
    exact Bool.le_iff_imp.mp (wireFn_mono (p+l) C hC.1 (p+l+j) (singletonInput_le q x hx)) hq
  obtain ⟨a,b,hab,hi0,hj1,hout⟩ := and_replacement_output_essential E C hC hmin j hj q.val hi hop hle
    (fun u => by rw [hinput, hsingle])
    (by intro heq; apply hneq; intro x; exact (heq x).trans (hinput x))
  exact ⟨a,b,hab,by simpa only [hinput] using hi0,hj1,hout⟩

end H5ReplacementEssential

namespace H5DeleteOr

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TwoColour
open H5Pruning H5Bridge H5Stars H5OrLift H5Owners

lemma delGate_orIn_subset (n g r : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hg : g < C.gates.length) (hr : r < n+g)
    (hgr : orIn n C r ⊆ orIn n C (n+g)) :
    ∀ w < n+(delGate n g r C).gates.length,
      orIn n (delGate n g r C) w ⊆ orIn n C (origWire n g w) := by
  classical
  have hD := delGate_isAO2 n g r C hAO hg hr
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · have ho : origWire n g w = w := by unfold origWire; split_ifs <;> omega
      rw [ho, H5Reach.orIn_input n C w hwn, H5Reach.orIn_input n (delGate n g r C) w hwn]
    · let k := w-n
      have he : w = n+k := by unfold k; omega
      have hk : k < (delGate n g r C).gates.length := by omega
      have hk' : k < C.gates.length-1 := by rwa [delGate_length n g r C hg] at hk
      let k0 := if k < g then k else k+1
      have hk0 : k0 < C.gates.length := by unfold k0; split_ifs <;> omega
      have ho : origWire n g (n+k) = n+k0 := by
        unfold origWire k0; split_ifs <;> omega
      rw [he, ho, H5Reach.orIn_gate n (delGate n g r C) hD.2.1 k hk,
        H5Reach.orIn_gate n C hAO.2.1 k0 hk0, delGate_gateAt n g r C hg k hk']
      simp only [mapGate]
      change (if (gateAt C k0).op = .or then
        ((gateAt C k0).inputs.map (remap n g r)).toFinset.biUnion
          (orIn n (delGate n g r C)) else ∅) ⊆
        (if (gateAt C k0).op = .or then (gateAt C k0).inputs.toFinset.biUnion
          (orIn n C) else ∅)
      by_cases hop : (gateAt C k0).op = .or
      · simp only [hop, ↓reduceIte]
        have himg : ((gateAt C k0).inputs.map (remap n g r)).toFinset =
            (gateAt C k0).inputs.toFinset.image (remap n g r) := by
          ext u
          simp
        rw [himg, Finset.image_biUnion]
        intro a ha
        obtain ⟨u, hu, hau⟩ := Finset.mem_biUnion.mp ha
        refine Finset.mem_biUnion.mpr ⟨u, hu, ?_⟩
        have hu' := List.mem_toFinset.mp hu
        have hru : remap n g r u < n+k := by
          apply hD.2.1 k hk
          rw [delGate_gateAt n g r C hg k hk']
          exact List.mem_map.mpr ⟨u,hu',rfl⟩
        have hs := ih _ (by omega) (by omega) hau
        by_cases hug : u = n+g
        · rw [hug, origWire_remap_eq n g r hr] at hs
          rw [hug]
          exact hgr hs
        · rwa [origWire_remap_ne n g r u hug] at hs
      · simp only [hop, ↓reduceIte]
        exact Finset.Subset.refl _


lemma delGate_tCount_zero (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (g r : ℕ) (hg : g < C.gates.length) (hr : r < n+g)
    (hreach : orIn n C r ⊆ orIn n C (n+g)) (lin : ℕ → Bool)
    (hT : tCount n C lin = 0) : tCount n (delGate n g r C) lin = 0 := by
  apply H5Reach.tCount_zero_of_orIn_subsets n C (delGate n g r C) lin hAO.2.1 hT
  intro j hj _
  exact ⟨origWire n g (n+j), delGate_orIn_subset n g r C hAO hg hr hreach
    (n+j) (by omega)⟩

lemma delGate_remap_ge (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length)
    (w : ℕ) (hw : n+C.gates.length ≤ w) :
    n+(delGate n g r C).gates.length ≤ remap n g r w := by
  rw [delGate_length n g r C hg]
  unfold remap
  split_ifs <;> omega

lemma delGate_mapped_eq_all (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n+g)
    (heq : wireFn n C (n+g) x = wireFn n C r x) (w : ℕ) :
    wireFn n (delGate n g r C) (remap n g r w) x = wireFn n C w x := by
  by_cases hw : w < n+C.gates.length
  · exact delGate_mapped_eq n g r C x hRB hg hr heq w hw
  · rw [wireFn_ge n C w (by omega), wireFn_ge n (delGate n g r C)
      (remap n g r w) (delGate_remap_ge n g r C hg w (by omega))]

lemma delGate_mapped_le_all (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hr : r < n+g)
    (hchild : wireFn n C r x = true → wireFn n C (n+g) x = true) (w : ℕ) :
    wireFn n (delGate n g r C) (remap n g r w) x ≤ wireFn n C w x := by
  by_cases hw : w < n+C.gates.length
  · exact Bool.le_iff_imp.mpr (delGate_mapped_le n g r C x hAO hg hr hchild w hw)
  · rw [wireFn_ge n C w (by omega), wireFn_ge n (delGate n g r C)
      (remap n g r w) (delGate_remap_ge n g r C hg w (by omega))]

lemma delGate_keepsStars (n g r : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hg : g < C.gates.length) (hr : r < n+g)
    (hchild : ∀ x, wireFn n C r x = true → wireFn n C (n+g) x = true)
    (hsingle : ∀ u, wireFn n C (n+g) (H5Pruning.singletonInput u) =
      wireFn n C r (H5Pruning.singletonInput u)) :
    KeepsStars n C (delGate n g r C) := by
  intro Q w hQ hs
  have hw := pure_star_valid n C Q (Finset.card_pos.mp (by omega)) w hs
  exact ⟨remap n g r w, delGate_pureStar n g r C hAO hg hr hchild hsingle w hw Q hs⟩

lemma delete_equal (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (g r : ℕ) (hg : g < C.gates.length) (hr : r < n+g)
    (hreach : orIn n C r ⊆ orIn n C (n+g))
    (heq : ∀ x, wireFn n C (n+g) x = wireFn n C r x)
    (lin : ℕ → Bool) (hT : tCount n C lin = 0) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
      (∀ x, wireFn n D D.output x = wireFn n C C.output x) ∧
      tCount n D lin = 0 ∧ KeepsStars n C D := by
  refine ⟨delGate n g r C, delGate_isAO2 n g r C hAO hg hr, ?_, ?_,
    delGate_tCount_zero n C hAO g r hg hr hreach lin hT, ?_⟩
  · change (delGate n g r C).gates.length < C.gates.length
    rw [delGate_length n g r C hg]
    omega
  · intro x
    exact delGate_mapped_eq_all n g r C x hAO.2.1 hg hr (heq x) C.output
  · exact delGate_keepsStars n g r C hAO hg hr (fun x hx => (heq x).trans hx)
      (fun u => heq (H5Pruning.singletonInput u))

lemma delGate_admissible_of_tests {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : admissible p l E C) (g r : ℕ) (hg : g < C.gates.length)
    (hop : (gateAt C g).op = .or) (hr : r ∈ (gateAt C g).inputs)
    (hsingle : ∀ u, wireFn (p+l) C (p+l+g) (H5Pruning.singletonInput u) =
      wireFn (p+l) C r (H5Pruning.singletonInput u))
    (hedge : ∀ a b, (a,b) ∈ E →
      wireFn (p+l) C (p+l+g) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) =
      wireFn (p+l) C r (pairInput (Fin.castAdd l a) (Fin.natAdd p b))) :
    admissible p l E (delGate (p+l) g r C) := by
  let D := delGate (p+l) g r C
  have hrlt : r < p+l+g := hC.1.2.1 g hg r hr
  have hAO : IsAO2 (p+l) D := delGate_isAO2 (p+l) g r C hC.1 hg hrlt
  have hchild : ∀ x, wireFn (p+l) C r x = true → wireFn (p+l) C (p+l+g) x = true :=
    or_child_imp C hC.1 g hg hop r hr
  have hreach : orIn (p+l) C r ⊆ orIn (p+l) C (p+l+g) := by
    intro a ha
    exact H5Reach.orIn_up (p+l) C g r a hg hop hr hrlt ha
  have hT := delGate_tCount_zero (p+l) C hC.1 g r hg hrlt hreach
    (fun i => decide (p ≤ i)) hC.2.2.1
  have hspec : ∀ x, wireFn (p+l) C C.output x = H5Pruning.graphFun (bipartiteEdges E) x := by
    intro x
    rw [graphFun_bipartite]
    exact hC.2.1 x
  have hfun : ∀ x, wireFn (p+l) D D.output x = H5Pruning.graphFun (bipartiteEdges E) x := by
    apply H5Essential.graph_eq_of_positive_and_le (p+l) (bipartiteEdges E)
      (wireFn (p+l) D D.output) (wireFn_mono (p+l) D hAO D.output)
    · intro x
      rw [← hspec x]
      exact delGate_mapped_le_all (p+l) g r C x hC.1 hg hrlt (hchild x) C.output
    · intro e he
      obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp he
      change wireFn (p+l) D (remap (p+l) g r C.output)
        (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true
      rw [delGate_mapped_eq_all (p+l) g r C _ hC.1.2.1 hg hrlt (hedge a b hab),
        hspec, graphFun_bipartite]
      exact decide_eq_true ⟨a,b,hab,by simp [pairInput],by simp [pairInput]⟩
  apply admissible_of_keeps E C D hC hAO _ hT
    (delGate_keepsStars (p+l) g r C hC.1 hg hrlt hchild hsingle)
  intro x
  exact (hfun x).trans (hspec x).symm

lemma or_child_private_test {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : admissible p l E C)
    (hmin : ∀ D, admissible p l E D → C.size ≤ D.size)
    (g r : ℕ) (hg : g < C.gates.length) (hop : (gateAt C g).op = .or)
    (hr : r ∈ (gateAt C g).inputs) :
    (∃ u, wireFn (p+l) C (p+l+g) (H5Pruning.singletonInput u) = true ∧
      wireFn (p+l) C r (H5Pruning.singletonInput u) = false) ∨
    (∃ (a : Fin p) (b : Fin l), (a,b) ∈ E ∧
      wireFn (p+l) C (p+l+g) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true ∧
      wireFn (p+l) C r (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = false) := by
  by_contra hbad
  have hchild : ∀ x, wireFn (p+l) C r x = true → wireFn (p+l) C (p+l+g) x = true :=
    or_child_imp C hC.1 g hg hop r hr
  have hsingle : ∀ u, wireFn (p+l) C (p+l+g) (H5Pruning.singletonInput u) =
      wireFn (p+l) C r (H5Pruning.singletonInput u) := by
    intro u
    cases hgval : wireFn (p+l) C (p+l+g) (H5Pruning.singletonInput u) <;>
      cases hrval : wireFn (p+l) C r (H5Pruning.singletonInput u)
    · rfl
    · have he := hchild _ hrval
      rw [hgval] at he
      cases he
    · exact False.elim (hbad (Or.inl ⟨u,hgval,hrval⟩))
    · rfl
  have hedge : ∀ a b, (a,b) ∈ E →
      wireFn (p+l) C (p+l+g) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) =
      wireFn (p+l) C r (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) := by
    intro a b hab
    cases hgval : wireFn (p+l) C (p+l+g) (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) <;>
      cases hrval : wireFn (p+l) C r (pairInput (Fin.castAdd l a) (Fin.natAdd p b))
    · rfl
    · have he := hchild _ hrval
      rw [hgval] at he
      cases he
    · exact False.elim (hbad (Or.inr ⟨a,b,hab,hgval,hrval⟩))
    · rfl
  have hD := delGate_admissible_of_tests E C hC g r hg hop hr hsingle hedge
  have hle := hmin (delGate (p+l) g r C) hD
  change C.gates.length ≤ (delGate (p+l) g r C).gates.length at hle
  rw [delGate_length (p+l) g r C hg] at hle
  omega

lemma or_operand_private_test {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : admissible p l E C)
    (hmin : ∀ D, admissible p l E D → C.size ≤ D.size)
    (g r s : ℕ) (hg : g < C.gates.length) (hop : (gateAt C g).op = .or)
    (hinp : (gateAt C g).inputs = [r,s] ∨ (gateAt C g).inputs = [s,r]) :
    (∃ u, wireFn (p+l) C r (H5Pruning.singletonInput u) = true ∧
      wireFn (p+l) C s (H5Pruning.singletonInput u) = false) ∨
    (∃ (a : Fin p) (b : Fin l), (a,b) ∈ E ∧
      wireFn (p+l) C r (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true ∧
      wireFn (p+l) C s (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = false) := by
  have hs : s ∈ (gateAt C g).inputs := by rcases hinp with h | h <;> simp [h]
  have hgate : ∀ x, wireFn (p+l) C (p+l+g) x =
      (wireFn (p+l) C r x || wireFn (p+l) C s x) := by
    intro x
    rw [H5LiftGlue.wireFn_gate (p+l) C hC.1.2.1 g hg,hop]
    rcases hinp with h | h
    · simp [h,GateOp.eval]
    · simp [h,GateOp.eval,Bool.or_comm]
  rcases or_child_private_test E C hC hmin g s hg hop hs with
      ⟨u, hgu, hsu⟩ | ⟨a,b,hab,hgab,hsab⟩
  · left
    refine ⟨u,?_,hsu⟩
    simpa only [hgate,hsu,Bool.or_false] using hgu
  · right
    refine ⟨a,b,hab,?_,hsab⟩
    simpa only [hgate,hsab,Bool.or_false] using hgab

end H5DeleteOr

end PEqualNP.Outside.L_meta_4970_aux
