import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448_aux.PivotalNecessary

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

lemma wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

lemma getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

lemma ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


lemma mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

lemma wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

lemma wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

lemma wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma snoc_mono (W : List Bool) (v v' : Bool) (h : v = true → v' = true) (i : ℕ) :
    (W ++ [v]).getD i false = true → (W ++ [v']).getD i false = true := by
  rcases Nat.lt_trichotomy i W.length with hi | hi | hi
  · rw [getD_snoc_lt _ _ _ hi, getD_snoc_lt _ _ _ hi]; exact id
  · subst hi; rw [getD_snoc_eq, getD_snoc_eq]; exact h
  · rw [getD_snoc_gt _ _ _ hi]; intro hf; exact absurd hf (by simp)

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma circuit_mono (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  apply mono2 C.gates
  · intro g hg
    simpa using hm g hg
  · simp
  · exact ofFn_mono n x y hxy

lemma graph_sandwich (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (hm : Monotone2 D)
    (hbelow : ∀ x : Fin n → Bool, circuitFun n D x = true → graphFun G ∅ x = true)
    (hedges : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  refine ⟨hbelow x, ?_⟩
  intro hx
  obtain ⟨u, v, huv, hu, hv⟩ : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    simpa [graphFun] using hx
  apply circuit_mono n D hm (pairInput u v) x _ (hedges u v huv)
  intro w hw
  have h : w = u ∨ w = v := of_decide_eq_true hw
  rcases h with rfl | rfl
  · exact hu
  · exact hv

lemma graph_rewrite (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hm : Monotone2 D) (hC : circuitFun n C = graphFun G ∅)
    (hdown : ∀ x : Fin n → Bool, circuitFun n D x = true → circuitFun n C x = true)
    (hedges : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = circuitFun n C := by
  rw [hC]
  apply graph_sandwich n G D hm _ hedges
  intro x hx
  rw [← hC]
  exact hdown x hx

lemma set_eval_mono (n j : ℕ) (C : Circuit) (hm : Monotone2 C)
    (hj : j < C.gates.length) (r s : Gate) (x : Fin n → Bool)
    (hle : r.op.eval (r.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) = true →
      s.op.eval (s.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) = true) :
    circuitFun n ⟨C.gates.set j r, C.output⟩ x = true →
    circuitFun n ⟨C.gates.set j s, C.output⟩ x = true := by
  change (wf (C.gates.set j r) (List.ofFn x)).getD C.output false = true →
    (wf (C.gates.set j s) (List.ofFn x)).getD C.output false = true
  have hs : ∀ t : Gate, C.gates.set j t =
      C.gates.take j ++ t :: C.gates.drop (j + 1) := by
    intro t
    rw [List.set_eq_take_append_cons_drop]
    simp [hj]
  rw [hs r, hs s, wf_append, wf_append, wf_cons, wf_cons]
  apply mono2 (C.gates.drop (j + 1))
  · intro g hg
    simpa using hm g (List.mem_of_mem_drop hg)
  · simp
  · exact snoc_mono _ _ _ hle

lemma set_eval_eq (n j : ℕ) (C : Circuit) (hm : Monotone2 C)
    (hj : j < C.gates.length) (r s : Gate) (x : Fin n → Bool)
    (heq : r.op.eval (r.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) =
      s.op.eval (s.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false)) :
    circuitFun n ⟨C.gates.set j r, C.output⟩ x =
    circuitFun n ⟨C.gates.set j s, C.output⟩ x := by
  apply Bool.eq_iff_iff.mpr
  exact ⟨set_eval_mono n j C hm hj r s x (by rw [heq]; exact id),
    set_eval_mono n j C hm hj s r x (by rw [heq]; exact id)⟩

lemma set_gate_val (n j : ℕ) (C : Circuit) (hj : j < C.gates.length)
    (r : Gate) (x : Fin n → Bool) :
    gateVal n ⟨C.gates.set j r, C.output⟩ j x =
      r.op.eval (r.inputs.map fun i =>
        (wf (C.gates.take j) (List.ofFn x)).getD i false) := by
  change (wf (C.gates.set j r) (List.ofFn x)).getD (n + j) false = _
  rw [List.set_eq_take_append_cons_drop]
  simp only [hj, ↓reduceIte]
  rw [wf_append, wf_cons]
  have hl : (wf (C.gates.take j) (List.ofFn x)).length = n + j := by
    rw [wf_len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  rw [wf_keep _ _ _ (by simp [hl]), ← hl, getD_snoc_eq]

def shift (m t i : ℕ) : ℕ := if i < m then i else if i = m then t else i - 1

def remap (m t : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shift m t)⟩

lemma getD_oob (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma shift_before (m t : ℕ) (w : List Bool) (hw : w.length ≤ m) (ht : m ≤ t) (i : ℕ) :
    w.getD (shift m t i) false = w.getD i false := by
  by_cases hi : i < m
  · simp [shift, hi]
  · by_cases he : i = m
    · subst i
      simp only [shift, lt_self_iff_false, ↓reduceIte]
      rw [getD_oob _ _ (by omega), getD_oob _ _ hw]
    · simp only [shift, hi, he, ↓reduceIte]
      rw [getD_oob _ _ (by omega), getD_oob _ _ (by omega)]

lemma remap_before (m t : ℕ) (gs : List Gate) : ∀ w : List Bool,
    w.length + gs.length ≤ m → m ≤ t → wf (gs.map (remap m t)) w = wf gs w := by
  induction gs with
  | nil => intros; rfl
  | cons g gs ih =>
    intro w hw ht
    simp only [List.map_cons, wf_cons]
    have hv : (remap m t g).op.eval ((remap m t g).inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [remap, List.map_map]
      congr 1
      exact List.map_congr_left fun i _ => shift_before m t w (by simp at hw; omega) ht i
    rw [hv]
    exact ih _ (by simp at hw ⊢; omega) ht

def Rel (m t : ℕ) (a b : List Bool) : Prop :=
  a.length = b.length + 1 ∧ m < a.length ∧
    ∀ i, b.getD (shift m t i) false = a.getD i false

lemma rel_snoc (m t : ℕ) (a b : List Bool) (v : Bool)
    (h : Rel m t a b) (ht : a.length ≤ t) : Rel m t (a ++ [v]) (b ++ [v]) := by
  obtain ⟨hl, hm, hv⟩ := h
  refine ⟨by simp [hl], by simp; omega, ?_⟩
  intro i
  by_cases he : i = m
  · subst i
    have hzero : a.getD m false = false := by
      have hvm := hv m
      simp only [shift, lt_self_iff_false, ↓reduceIte] at hvm
      rw [getD_oob b t (by omega)] at hvm
      exact hvm.symm
    simp only [shift, lt_self_iff_false, ↓reduceIte]
    rw [getD_oob _ _ (by simp; omega), getD_snoc_lt _ _ _ hm, hzero]
  · rcases Nat.lt_trichotomy i a.length with hi | hi | hi
    · have hs : shift m t i < b.length := by
        unfold shift
        split_ifs <;> omega
      rw [getD_snoc_lt _ _ _ hs, getD_snoc_lt _ _ _ hi, hv]
    · have hs : shift m t i = b.length := by
        unfold shift
        split_ifs <;> omega
      rw [hs, getD_snoc_eq, hi, getD_snoc_eq]
    · have hs : b.length < shift m t i := by
        unfold shift
        split_ifs <;> omega
      rw [getD_snoc_gt _ _ _ hs, getD_snoc_gt _ _ _ hi]

lemma rel_fold (m t : ℕ) (gs : List Gate) : ∀ a b : List Bool,
    Rel m t a b → a.length + gs.length ≤ t →
      Rel m t (wf gs a) (wf (gs.map (remap m t)) b) := by
  induction gs with
  | nil => intro a b h _; exact h
  | cons g gs ih =>
    intro a b h ht
    simp only [List.map_cons, wf_cons]
    have hv : (remap m t g).op.eval ((remap m t g).inputs.map fun i => b.getD i false) =
        g.op.eval (g.inputs.map fun i => a.getD i false) := by
      simp only [remap, List.map_map]
      congr 1
      exact List.map_congr_left fun i _ => h.2.2 i
    rw [hv]
    apply ih
    · exact rel_snoc m t a b _ h (by simp at ht; omega)
    · simp at ht ⊢; omega

def eraseZero (n k : ℕ) (C : Circuit) : Circuit :=
  ⟨(C.gates.eraseIdx k).map (remap (n + k) (n + C.gates.length)),
    shift (n + k) (n + C.gates.length) C.output⟩

lemma eraseZero_fun (n k : ℕ) (C : Circuit) (hk : k < C.gates.length) :
    circuitFun n (eraseZero n k C) =
      circuitFun n ⟨C.gates.set k ⟨GateOp.or, []⟩, C.output⟩ := by
  funext x
  let w := wf (C.gates.take k) (List.ofFn x)
  have hl : w.length = n + k := by
    simp [w, wf_len, List.length_take, Nat.min_eq_left hk.le]
  have hpre : wf ((C.gates.take k).map (remap (n + k) (n + C.gates.length)))
      (List.ofFn x) = w := by
    apply remap_before
    · simp [List.length_take, Nat.min_eq_left hk.le]
    · omega
  have hzero : Rel (n + k) (n + C.gates.length) (w ++ [false]) w := by
    refine ⟨by simp, by simp [hl], ?_⟩
    intro i
    rcases Nat.lt_trichotomy i (n + k) with hi | hi | hi
    · simp only [shift, hi, ↓reduceIte]
      exact (getD_snoc_lt w false i (by omega)).symm
    · subst i
      simp only [shift, lt_self_iff_false, ↓reduceIte]
      rw [getD_oob _ _ (by omega), ← hl, getD_snoc_eq]
    · have hs : shift (n + k) (n + C.gates.length) i = i - 1 := by
        unfold shift
        split_ifs <;> omega
      rw [hs, getD_oob _ _ (by omega), getD_snoc_gt _ _ _ (by omega)]
  have hrel := rel_fold (n + k) (n + C.gates.length) (C.gates.drop (k + 1))
    (w ++ [false]) w hzero (by simp [hl, List.length_drop]; omega)
  change (wf (eraseZero n k C).gates (List.ofFn x)).getD
      (eraseZero n k C).output false =
    (wf (C.gates.set k ⟨GateOp.or, []⟩) (List.ofFn x)).getD C.output false
  simp only [eraseZero, List.eraseIdx_eq_take_drop_succ, List.map_append, wf_append, hpre]
  rw [List.set_eq_take_append_cons_drop]
  simp only [hk, ↓reduceIte, wf_append, wf_cons, GateOp.eval, List.map_nil,
    List.any_nil]
  exact hrel.2.2 C.output

lemma eraseZero_mono (n k : ℕ) (C : Circuit) (hm : Monotone2 C) :
    Monotone2 (eraseZero n k C) := by
  intro g hg
  simp only [eraseZero, List.mem_map] at hg
  obtain ⟨h, hh, rfl⟩ := hg
  simpa [remap] using hm h (List.mem_of_mem_eraseIdx hh)

lemma eraseZero_size (n k : ℕ) (C : Circuit) (hk : k < C.gates.length) :
    (eraseZero n k C).size + 1 = C.size := by
  simp only [Circuit.size, eraseZero, List.length_map, List.length_eraseIdx, hk, ↓reduceIte]
  omega

lemma every_gate_has_pivotal_edge (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : Monotone2 C) (hfun : circuitFun n C = graphFun G ∅)
    (hmin : ∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ → C.size ≤ D.size)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ u v : Fin n, G.Adj u v ∧
      circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ (pairInput u v) = false := by
  classical
  by_contra hnone
  let z : Gate := ⟨GateOp.or, []⟩
  let Z : Circuit := ⟨C.gates.set j z, C.output⟩
  have hZm : Monotone2 Z := by
    intro g hg
    rcases List.mem_or_eq_of_mem_set hg with hg | rfl
    · exact hm g hg
    · simp [z]
  have hsame : (⟨C.gates.set j C.gates[j], C.output⟩ : Circuit) = C := by simp
  have hZf : circuitFun n Z = graphFun G ∅ := by
    apply graph_sandwich n G Z hZm
    · intro x hx
      rw [← hfun]
      rw [← hsame]
      exact set_eval_mono n j C hm hj z C.gates[j] x (by simp [z, GateOp.eval]) hx
    · intro u v huv
      cases h : circuitFun n Z (pairInput u v) with
      | true => rfl
      | false => exact (hnone ⟨u, v, huv, h⟩).elim
  have hd := hmin (eraseZero n j C) (eraseZero_mono n j C hm)
    ((eraseZero_fun n j C hj).trans hZf)
  have hs := eraseZero_size n j C hj
  omega

end PEqualNP.Outside.L_meta_2448_aux.PivotalNecessary
