import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650.Pruning
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

lemma wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

lemma gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

lemma wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

lemma wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

def ren (n m p i : ℕ) : ℕ := if i = n + m then p else if n + m < i then i - 1 else i

def rg (n m p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren n m p)⟩

lemma sim (n m p : ℕ) (hp : p < n + m) (B : List Gate) : ∀ U U' : List Bool, U.length = U'.length + 1 →
    n + m < U.length → (∀ i, U.getD i false = U'.getD (ren n m p i) false) →
    ∀ i, (wf B U).getD i false = (wf (B.map (rg n m p)) U').getD (ren n m p i) false := by
  induction B with
  | nil => intro U U' _ _ h i; exact h i
  | cons g B ih =>
    intro U U' hlen hbig h i
    rw [List.map_cons, wf_cons, wf_cons]
    refine ih _ _ (by simp [hlen]) (by simp; omega) ?_ i
    intro t
    have hv : g.op.eval (g.inputs.map fun i => U.getD i false)
        = (rg n m p g).op.eval ((rg n m p g).inputs.map fun i => U'.getD i false) := by
      show _ = g.op.eval ((g.inputs.map (ren n m p)).map fun i => U'.getD i false)
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h i
    rw [← hv]
    rcases Nat.lt_trichotomy t U.length with ht | ht | ht
    · have h1 : ren n m p t < U'.length := by
        unfold ren
        split
        · omega
        · split <;> omega
      rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ h1]
      exact h t
    · subst ht
      rw [getD_snoc_eq]
      have e : ren n m p U.length = U'.length := by
        unfold ren
        rw [ite_eq_right (by omega), ite_eq_left hbig]
        omega
      rw [e, getD_snoc_eq]
    · rw [getD_snoc_gt _ _ _ ht]
      have e : U'.length < ren n m p t := by
        unfold ren
        rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        omega
      rw [getD_snoc_gt _ _ _ e]

lemma erase_spec : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (m p : ℕ), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → m < C.gates.length → p < n + m → PEqualNP.MetaComplexity.Monotone2 (PEqualNP.CircuitMoves.eraseGate n C m p) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n (PEqualNP.CircuitMoves.eraseGate n C m p) ∧ (PEqualNP.CircuitMoves.eraseGate n C m p).size + 1 = C.size ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD p false = (C.wires (List.ofFn x)).getD (n + m) false → (PEqualNP.CircuitMoves.eraseGate n C m p).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  intro n C m p hmono hrb hm hp
  have hE : PEqualNP.CircuitMoves.eraseGate n C m p
      = ⟨C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p), ren n m p C.output⟩ := by
    unfold PEqualNP.CircuitMoves.eraseGate
    rw [if_pos hm]
    rfl
  rw [hE]
  have hG : ∀ j (hj : j < C.gates.length),
      PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
    intro j hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ hj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g0, hg0, rfl⟩
    · exact hmono g (List.mem_of_mem_take hg)
    · have := hmono g0 (List.mem_of_mem_drop hg0)
      exact ⟨this.1, by simpa [rg] using this.2⟩
  · intro j hj i hi
    have hlen : (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p)).length = C.gates.length - 1 := by
      simp; omega
    have hj' : j < C.gates.length - 1 := by
      have : j < (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p)).length := hj
      omega
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    by_cases hjm : j < m
    · have e : (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p)).getD j ⟨GateOp.or, []⟩ = C.gates[j]'(by omega) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append, hjm, List.getElem?_take, (by omega : j < C.gates.length)]
      rw [e] at hi
      have := hrb j (by omega) i
      rw [hG j (by omega)] at this
      exact this hi
    · have e : (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p)).getD j ⟨GateOp.or, []⟩ = rg n m p (C.gates[j + 1]'(by omega)) := by
        have h1 : m + 1 + (j - m) = j + 1 := by omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_append, hjm, List.getElem?_take, List.getElem?_drop, h1, (by omega : j + 1 < C.gates.length), (by omega : min m C.gates.length = m)]
      rw [e] at hi
      simp only [rg, List.mem_map] at hi
      obtain ⟨i0, hi0, rfl⟩ := hi
      have := hrb (j + 1) (by omega) i0
      rw [hG (j + 1) (by omega)] at this
      have h0 := this hi0
      unfold ren
      split
      · omega
      · split <;> omega
  · simp [Circuit.size]; omega
  · intro x hx
    have h2 : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
      rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
    have hWlen : (wf (C.gates.take m) (List.ofFn x)).length = n + m := by
      rw [wf_len, List.length_ofFn, List.length_take, Nat.min_eq_left (le_of_lt hm)]
    have e1 : wf C.gates (List.ofFn x) = wf (C.gates.drop (m + 1))
        (wf (C.gates.take m) (List.ofFn x) ++ [C.gates[m].op.eval (C.gates[m].inputs.map fun i => (wf (C.gates.take m) (List.ofFn x)).getD i false)]) := by
      conv_lhs => rw [h2]
      rw [wf_append, wf_cons]
    show (wf (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p)) (List.ofFn x)).getD (ren n m p C.output) false
      = (wf C.gates (List.ofFn x)).getD C.output false
    have hx' : (wf C.gates (List.ofFn x)).getD p false = (wf C.gates (List.ofFn x)).getD (n + m) false := hx
    rw [wf_append, e1]
    rw [e1] at hx'
    generalize wf (C.gates.take m) (List.ofFn x) = W at *
    generalize C.gates[m].op.eval (C.gates[m].inputs.map fun i => W.getD i false) = v at *
    rw [wf_keep _ _ _ (by simp; omega), wf_keep _ _ _ (by simp; omega), getD_snoc_lt _ _ _ (by omega)] at hx'
    have hv : (W ++ [v]).getD (n + m) false = v := by rw [← hWlen, getD_snoc_eq]
    rw [hv] at hx'
    refine (sim n m p hp (C.gates.drop (m + 1)) (W ++ [v]) W (by simp) (by simp; omega) ?_ C.output).symm
    intro i
    unfold ren
    split
    · rename_i h; rw [h, hv, hx']
    · split
      · rw [getD_snoc_gt _ _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      · rw [getD_snoc_lt _ _ _ (by omega)]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hk]

lemma evalT (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (ins.map f) = true → op.eval (ins.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

lemma evalb (b : Bool) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = b → f' i = b) :
    op.eval (ins.map f) = b → op.eval (ins.map f') = b := by
  cases b
  · intro hf
    by_contra hc
    have hc' : op.eval (ins.map f') = true := by simpa using hc
    have h3 := evalT op hop ins f' f (fun i hi => by
      by_contra hn
      have h4 := h i (by simpa using hn)
      rw [h4] at hi
      exact absurd hi (by simp)) hc'
    rw [hf] at h3
    exact absurd h3 (by simp)
  · exact evalT op hop ins f f' h

lemma simb (b : Bool) (n m p : ℕ) (B : List Gate)
    (hB : ∀ g ∈ B, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ U U' : List Bool, U.length = U'.length + 1 → n + m < U.length →
    (p < n + m ∨ U'.length + B.length < p) →
    (∀ i, U.getD i false = b → U'.getD (ren n m p i) false = b) →
    ∀ i, (wf B U).getD i false = b → (wf (B.map (rg n m p)) U').getD (ren n m p i) false = b := by
  induction B with
  | nil => intro U U' _ _ _ h i; exact h i
  | cons g B ih =>
    intro U U' hlen hbig hp h i
    rw [List.map_cons, wf_cons, wf_cons]
    refine ih (fun g' hg' => hB g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hlen])
      (by simp; omega) ?_ ?_ i
    · rcases hp with hp | hp
      · exact Or.inl hp
      · right
        simp only [List.length_cons, List.length_append, List.length_nil] at hp ⊢
        omega
    · intro t ht
      have hv : g.op.eval (g.inputs.map fun i => U.getD i false) = b →
          (rg n m p g).op.eval ((rg n m p g).inputs.map fun i => U'.getD i false) = b := by
        intro hb
        show g.op.eval ((g.inputs.map (ren n m p)).map fun i => U'.getD i false) = b
        rw [List.map_map]
        exact evalb b g.op (hB g (List.mem_cons_self ..)) g.inputs _ _ (fun i hi => h i hi) hb
      rcases Nat.lt_trichotomy t U.length with htl | htl | htl
      · rw [getD_snoc_lt _ _ _ htl] at ht
        have h0 := h t ht
        by_cases htm : t = n + m
        · have e : ren n m p t = p := by unfold ren; rw [if_pos htm]
          rw [e] at h0 ⊢
          rcases hp with hp | hp
          · rw [getD_snoc_lt _ _ _ (by omega)]; exact h0
          · simp only [List.length_cons] at hp
            rw [getD_snoc_gt _ _ _ (by omega)]
            rw [List.getD_eq_default _ _ (by omega)] at h0
            exact h0
        · have h1 : ren n m p t < U'.length := by
            unfold ren
            rw [if_neg htm]
            split <;> omega
          rw [getD_snoc_lt _ _ _ h1]; exact h0
      · subst htl
        rw [getD_snoc_eq] at ht
        have e : ren n m p U.length = U'.length := by
          unfold ren
          rw [if_neg (by omega), if_pos hbig]
          omega
        rw [e, getD_snoc_eq]; exact hv ht
      · rw [getD_snoc_gt _ _ _ htl] at ht
        have e : U'.length < ren n m p t := by
          unfold ren
          rw [if_neg (by omega), if_pos (by omega)]
          omega
        rw [getD_snoc_gt _ _ _ e]; exact ht

lemma erase_eq (n : ℕ) (C : Circuit) (m p : ℕ) (hml : m < C.gates.length) :
    PEqualNP.CircuitMoves.eraseGate n C m p
      = ⟨C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p), ren n m p C.output⟩ := by
  unfold PEqualNP.CircuitMoves.eraseGate
  rw [if_pos hml]
  rfl

lemma erase_sim (n : ℕ) (C : Circuit) (m p : ℕ) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hml : m < C.gates.length) (hp : p < n + m ∨ p = n + C.gates.length) (x : List Bool)
    (hx : x.length = n) (b : Bool)
    (hb : (wf C.gates x).getD (n + m) false = b → (wf C.gates x).getD p false = b) (w : ℕ)
    (hw : (wf C.gates x).getD w false = b) :
    (wf (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p)) x).getD (ren n m p w) false = b := by
  have h2 : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
    rw [← List.drop_eq_getElem_cons hml, List.take_append_drop]
  have hWlen : (wf (C.gates.take m) x).length = n + m := by
    rw [wf_len, hx, List.length_take, Nat.min_eq_left (le_of_lt hml)]
  have e1 : wf C.gates x = wf (C.gates.drop (m + 1))
      (wf (C.gates.take m) x ++ [C.gates[m].op.eval (C.gates[m].inputs.map fun i => (wf (C.gates.take m) x).getD i false)]) := by
    conv_lhs => rw [h2]
    rw [wf_append, wf_cons]
  have hfull : (wf C.gates x).length = n + C.gates.length := by rw [wf_len, hx]
  rw [wf_append]
  rw [e1] at hw hb
  have hdl : (C.gates.drop (m + 1)).length = C.gates.length - (m + 1) := List.length_drop
  refine simb b n m p (C.gates.drop (m + 1))
    (fun g hg => (hm g (List.mem_of_mem_drop hg)).1) _ _ (by simp) (by simp; omega) ?_ ?_ w hw
  · rcases hp with hp | hp
    · exact Or.inl hp
    · right; rw [hWlen, hdl, hp]; omega
  · intro i hi
    unfold ren
    split
    · rename_i hinm
      subst hinm
      rw [wf_keep _ _ _ (by simp; omega)] at hb
      have h3 := hb hi
      rcases hp with hp | hp
      · rw [wf_keep _ _ _ (by simp; omega), getD_snoc_lt _ _ _ (by omega)] at h3
        exact h3
      · rw [← e1, List.getD_eq_default _ _ (by rw [hfull, hp])] at h3
        rw [List.getD_eq_default _ _ (by rw [hWlen, hp]; omega)]
        exact h3
    · split
      · rw [getD_snoc_gt _ _ _ (by omega)] at hi
        rw [List.getD_eq_default _ _ (by omega)]
        exact hi
      · rw [getD_snoc_lt _ _ _ (by omega)] at hi
        exact hi

lemma wf_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (U V : List Bool) (hlen : U.length = V.length)
    (hUV : ∀ i, U.getD i false = true → V.getD i false = true) :
    ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs generalizing U V with
  | nil => exact hUV
  | cons g gs ih =>
    rw [wf_cons, wf_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hlen])
    intro i hi
    rcases Nat.lt_trichotomy i U.length with h | h | h
    · rw [getD_snoc_lt _ _ _ h] at hi
      rw [getD_snoc_lt _ _ _ (by omega)]
      exact hUV i hi
    · subst i
      rw [getD_snoc_eq] at hi
      rw [hlen, getD_snoc_eq]
      exact evalT g.op (hgs g (List.mem_cons_self ..)) g.inputs _ _ hUV hi
    · rw [getD_snoc_gt _ _ _ h] at hi
      exact Bool.noConfusion hi

lemma wires_mono {n : ℕ} (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    ∀ w, (C.wires (List.ofFn x)).getD w false = true →
      (C.wires (List.ofFn y)).getD w false = true := by
  apply wf_mono C.gates (fun g hg => (hm g hg).1) _ _ (by simp)
  intro i hi
  by_cases h : i < n
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h] using
      hxy ⟨i, h⟩ (by simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h] using hi)
  · simp [List.getD_eq_getElem?_getD, h] at hi

lemma input_wire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    (C.wires (List.ofFn x)).getD p.val false = x p := by
  change (wf C.gates (List.ofFn x)).getD p.val false = x p
  rw [wf_keep _ _ _ (by simpa using p.isLt)]
  simp [List.getD_eq_getElem?_getD, p.isLt]

lemma erase_preserves_edge_function
    {n : ℕ} (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hr : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (m : ℕ) (hmidx : m < C.gates.length) (p : Fin n)
    (E : Fin n → Fin n → Prop)
    (correct : ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = true ↔ ∃ u v, E u v ∧ x u = true ∧ x v = true)
    (singleton : (C.wires (List.ofFn (fun i : Fin n => decide (i = p)))).getD
      (n + m) false = true)
    (pairs : ∀ u v, E u v →
      (C.wires (List.ofFn (fun i : Fin n => decide (i = u ∨ i = v)))).getD
        (n + m) false = decide (p = u ∨ p = v)) :
    PEqualNP.MetaComplexity.Monotone2 (PEqualNP.CircuitMoves.eraseGate n C m p.val) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack n
        (PEqualNP.CircuitMoves.eraseGate n C m p.val) ∧
      (PEqualNP.CircuitMoves.eraseGate n C m p.val).size + 1 = C.size ∧
      ∀ x : Fin n → Bool,
        (PEqualNP.CircuitMoves.eraseGate n C m p.val).eval (List.ofFn x) = true ↔
          ∃ u v, E u v ∧ x u = true ∧ x v = true := by
  have hp : p.val < n + m := by omega
  obtain ⟨mono, back, size, eqval⟩ := erase_spec n C m p.val hm hr hmidx hp
  refine ⟨mono, back, size, ?_⟩
  let D := PEqualNP.CircuitMoves.eraseGate n C m p.val
  have lower : ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = false → D.eval (List.ofFn x) = false := by
    intro x hfalse
    have dom : x p = true → (C.wires (List.ofFn x)).getD (n + m) false = true := by
      intro hxp
      apply wires_mono C hm (fun i : Fin n => decide (i = p)) x _ (n + m) singleton
      intro i hi
      have hip : i = p := of_decide_eq_true hi
      simpa [hip] using hxp
    have hb : (wf C.gates (List.ofFn x)).getD (n + m) false = false →
        (wf C.gates (List.ofFn x)).getD p.val false = false := by
      intro hg
      change (C.wires (List.ofFn x)).getD p.val false = false
      rw [input_wire]
      cases hxp : x p with
      | false => rfl
      | true =>
        have yes := dom hxp
        exact Bool.noConfusion (hg.symm.trans yes)
    have hs := erase_sim n C m p.val hm hmidx (Or.inl hp) (List.ofFn x)
      (by simp) false hb C.output hfalse
    simpa only [D, erase_eq n C m p.val hmidx, Circuit.eval, Circuit.wires, wf] using hs
  intro x
  constructor
  · intro hx
    apply (correct x).mp
    cases hC : C.eval (List.ofFn x) with
    | true => rfl
    | false =>
      have hD := lower x hC
      rw [hD] at hx
      exact Bool.noConfusion hx
  · rintro ⟨u, v, huv, hu, hv⟩
    let edge := fun i : Fin n => decide (i = u ∨ i = v)
    have hedge : ∀ i, edge i = true → x i = true := by
      intro i hi
      rcases of_decide_eq_true hi with rfl | rfl
      · exact hu
      · exact hv
    have hwire : (C.wires (List.ofFn edge)).getD p.val false =
        (C.wires (List.ofFn edge)).getD (n + m) false := by
      rw [input_wire]
      exact (pairs u v huv).symm
    have hC : C.eval (List.ofFn edge) = true :=
      (correct edge).mpr ⟨u, v, huv, by simp [edge], by simp [edge]⟩
    have hD : D.eval (List.ofFn edge) = true := (eqval edge hwire).trans hC
    exact wires_mono D mono edge x hedge D.output hD

end PEqualNP.Outside.L_meta_650.Pruning
