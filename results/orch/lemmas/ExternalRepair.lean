import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448_aux.ExternalRepair

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

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

lemma gate_val_eq (n j : ℕ) (C : Circuit) (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    gateVal n C j x = C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) := by
  change (wf C.gates (List.ofFn x)).getD (n+j) false = _
  have hs : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j+1) := by
    have hs : C.gates.set j C.gates[j] =
        C.gates.take j ++ C.gates[j] :: C.gates.drop (j+1) := by
      rw [List.set_eq_take_append_cons_drop]
      simp [hj]
    simpa using hs
  conv_lhs => rw [hs]
  rw [wf_append, wf_cons]
  have hl : (wf (C.gates.take j) (List.ofFn x)).length = n+j := by
    simp [wf_len, List.length_take, Nat.min_eq_left hj.le]
  rw [wf_keep _ _ _ (by simp [hl]), ← hl, getD_snoc_eq]

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

set_option maxHeartbeats 800000 in
lemma gate_semantic_le (n : ℕ) (C D : Circuit) (hm : Monotone2 C)
    (hlen : D.gates.length = C.gates.length) (hout : D.output = C.output)
    (x : Fin n → Bool)
    (hexc : ∀ k (hk : k < C.gates.length), D.gates[k] ≠ C.gates[k] →
      gateVal n D k x = true → gateVal n C k x = true) :
    circuitFun n D x = true → circuitFun n C x = true := by
  classical
  have hall : ∀ k, k ≤ C.gates.length → ∀ w,
      (wf (D.gates.take k) (List.ofFn x)).getD w false = true →
      (wf (C.gates.take k) (List.ofFn x)).getD w false = true := by
    intro k
    induction k with
    | zero => intro _ _; exact id
    | succ k ih =>
      intro hk w
      have hkC : k < C.gates.length := by omega
      have hkD : k < D.gates.length := by omega
      have ih := ih (by omega)
      have hlC : (wf (C.gates.take k) (List.ofFn x)).length = n+k := by
        simp [wf_len, List.length_take, Nat.min_eq_left hkC.le]
      have hlD : (wf (D.gates.take k) (List.ofFn x)).length = n+k := by
        simp [wf_len, List.length_take, Nat.min_eq_left hkD.le]
      have hval : D.gates[k].op.eval (D.gates[k].inputs.map fun i =>
          (wf (D.gates.take k) (List.ofFn x)).getD i false) = true →
          C.gates[k].op.eval (C.gates[k].inputs.map fun i =>
          (wf (C.gates.take k) (List.ofFn x)).getD i false) = true := by
        by_cases heq : D.gates[k] = C.gates[k]
        · rw [heq]
          apply eval_mono
          · exact (hm C.gates[k] (List.getElem_mem _)).1
          · exact ih
        · have hh := hexc k hkC heq
          rw [gate_val_eq n k D hkD, gate_val_eq n k C hkC] at hh
          exact hh
      rw [List.take_succ_eq_append_getElem hkD, List.take_succ_eq_append_getElem hkC,
        wf_snoc, wf_snoc]
      rcases Nat.lt_trichotomy w (n+k) with hw | hw | hw
      · rw [getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ (by omega)]
        exact ih w
      · rw [hw, ← hlD, getD_snoc_eq, hlD, ← hlC, getD_snoc_eq]
        exact hval
      · rw [getD_snoc_gt _ _ _ (by omega)]
        simp
  have he := hall C.gates.length (by rfl) C.output
  rw [← hlen, List.take_length, hlen, List.take_length] at he
  change (wf D.gates (List.ofFn x)).getD D.output false = true → _
  rw [hout]
  exact he

lemma binary_gate_value (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (op : GateOp) (u v : ℕ) (hgate : C.gates[j] = ⟨op,[u,v]⟩)
    (hu : u < n+j) (hv : v < n+j) (x : Fin n → Bool) :
    gateVal n C j x = op.eval [(C.wires (List.ofFn x)).getD u false,
      (C.wires (List.ofFn x)).getD v false] := by
  rw [gate_val_eq n j C hj, hgate]
  simp only [List.map_cons, List.map_nil]
  rw [← wire_take C.gates (List.ofFn x) j u (by simpa using hu) hj.le,
    ← wire_take C.gates (List.ofFn x) j v (by simpa using hv) hj.le]
  rfl

set_option maxHeartbeats 800000 in
lemma external_reader_repair (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hmC : Monotone2 C) (hmD : Monotone2 D)
    (hC : circuitFun n C = graphFun G ∅)
    (hlen : D.gates.length = C.gates.length) (hout : D.output = C.output)
    (g h t : ℕ) (hgt : g < t) (hht : h < t) (ht : t < C.gates.length)
    (hCt : C.gates[t] = ⟨GateOp.and, [n+g,n+h]⟩)
    (hDt : D.gates[t] = ⟨GateOp.or, [n+g,n+h]⟩)
    (hkeep : ∀ k (hk : k < C.gates.length), k ≠ g → k ≠ h → k ≠ t →
      D.gates[k] = C.gates[k])
    (hcleang : ∀ x : Fin n → Bool, gateVal n D g x = true → graphFun G ∅ x = true)
    (hcleanh : ∀ x : Fin n → Bool, gateVal n D h x = true → graphFun G ∅ x = true)
    (hcover : ∀ u v : Fin n, G.Adj u v →
      (gateVal n C g (pairInput u v) = true ∨ gateVal n C h (pairInput u v) = true) →
      gateVal n D g (pairInput u v) = true ∨ gateVal n D h (pairInput u v) = true)
    (hreach : ∀ x : Fin n → Bool, gateVal n D t x = true → circuitFun n D x = true) :
    circuitFun n D = graphFun G ∅ := by
  have htD : t < D.gates.length := by omega
  have evalC : ∀ x : Fin n → Bool,
      gateVal n C t x = (gateVal n C g x && gateVal n C h x) := by
    intro x
    rw [binary_gate_value n C t ht GateOp.and (n+g) (n+h) hCt (by omega) (by omega)]
    simp [GateOp.eval, gateVal]
  have evalD : ∀ x : Fin n → Bool,
      gateVal n D t x = (gateVal n D g x || gateVal n D h x) := by
    intro x
    rw [binary_gate_value n D t htD GateOp.or (n+g) (n+h) hDt (by omega) (by omega)]
    simp [GateOp.eval, gateVal]
  apply graph_sandwich n G D hmD
  · intro x hx
    by_contra hf
    have hc : circuitFun n C x = true := by
      apply gate_semantic_le n C D hmC hlen hout x ?_ hx
      intro k hk hneq hDk
      by_cases hkg : k = g
      · subst k; exact (hf (hcleang x hDk)).elim
      by_cases hkh : k = h
      · subst k; exact (hf (hcleanh x hDk)).elim
      by_cases hkt : k = t
      · subst k
        rw [evalD, Bool.or_eq_true] at hDk
        rcases hDk with hd | hd
        · exact (hf (hcleang x hd)).elim
        · exact (hf (hcleanh x hd)).elim
      · exact (hneq (hkeep k hk hkg hkh hkt)).elim
    rw [hC] at hc
    exact hf hc
  · intro u v huv
    let x := pairInput u v
    by_cases hactive : gateVal n C g x = true ∨ gateVal n C h x = true
    · apply hreach x
      rw [evalD, Bool.or_eq_true]
      exact hcover u v huv hactive
    · have hg0 : gateVal n C g x = false := Bool.eq_false_iff.mpr (fun h => hactive (Or.inl h))
      have hh0 : gateVal n C h x = false := Bool.eq_false_iff.mpr (fun h => hactive (Or.inr h))
      have ht0 : gateVal n C t x = false := by rw [evalC, hg0]; rfl
      have hCx : circuitFun n C x = true := by
        rw [hC]
        simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
          Bool.false_or, decide_eq_true_eq]
        exact ⟨u, v, huv, by simp [x, pairInput], by simp [x, pairInput]⟩
      apply gate_semantic_le n D C hmD hlen.symm hout.symm x ?_ hCx
      intro k hk hneq hCk
      have hkC : k < C.gates.length := by omega
      by_cases hkg : k = g
      · subst k; rw [hg0] at hCk; contradiction
      by_cases hkh : k = h
      · subst k; rw [hh0] at hCk; contradiction
      by_cases hkt : k = t
      · subst k; rw [ht0] at hCk; contradiction
      · exact (hneq (hkeep k hkC hkg hkh hkt).symm).elim

end PEqualNP.Outside.L_meta_2448_aux.ExternalRepair
